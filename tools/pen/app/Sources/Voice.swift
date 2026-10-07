import AVFoundation
import FoundationModels
import Speech
import SwiftUI

// Voice: squeeze and hold the Pencil, speak, let go. What was said is heard
// on the iPad (speech recognition, with the text's headings and rule names as
// its vocabulary), turned into one action by the on-device language model,
// and done; the thing an action names (a section, a rule, a line, words) is
// found by the app itself (Find.swift). Only a failure is spoken back.

/// What was said, as the language model reads it: one action, and what it names.
@Generable
struct VoiceCommand {
    @Guide(description: "The one action the user asked for")
    var action: VoiceAction
    @Guide(description: "For goToSection, goToRule and find: the words naming what to go to, as said; otherwise empty")
    var target: String
    @Guide(description: "For goToLine: the line number; otherwise 0")
    var line: Int
    @Guide(description: "For selectTool: the tool; otherwise pen")
    var tool: VoiceTool
    @Guide(description: "For lineNumbers and sectionsPanel: true to show, false to hide; otherwise true")
    var show: Bool
}

@Generable
enum VoiceAction {
    case goToSection, goToRule, goToLine, find, nextSection, previousSection, top, bottom
    case selectTool, recognise, undo, clearInk, lineNumbers, sectionsPanel, notUnderstood
}

@Generable
enum VoiceTool { case pen, eraser, lasso, move, revert }

/// What the app does for what was said.
enum Command: Equatable {
    case goTo(FindKind, String)
    case line(Int)
    case nextSection, previousSection, top, bottom
    case tool(PenTool)
    case recognise, undo, clearInk
    case lineNumbers(Bool)
    case sections(Bool)
    case notUnderstood

    init(_ c: VoiceCommand) {
        switch c.action {
        case .goToSection: self = .goTo(.section, c.target)
        case .goToRule: self = .goTo(.rule, c.target)
        case .find: self = .goTo(.anything, c.target)
        case .goToLine: self = .line(c.line)
        case .nextSection: self = .nextSection
        case .previousSection: self = .previousSection
        case .top: self = .top
        case .bottom: self = .bottom
        case .selectTool:
            switch c.tool {
            case .pen: self = .tool(.pen)
            case .eraser: self = .tool(.eraser)
            case .lasso: self = .tool(.lasso)
            case .move: self = .tool(.move)
            case .revert: self = .tool(.revert)
            }
        case .recognise: self = .recognise
        case .undo: self = .undo
        case .clearInk: self = .clearInk
        case .lineNumbers: self = .lineNumbers(c.show)
        case .sectionsPanel: self = .sections(c.show)
        case .notUnderstood: self = .notUnderstood
        }
    }

    /// The model's reading, held to what was said: a target it names that was
    /// not said (it borrows one from its instructions when nothing fits) is
    /// not understood, and an end of the text taken for a target is the end.
    func checked(against said: String) -> Command {
        guard case .goTo(_, let target) = self else { return self }
        switch Set(spokenWords(target)) {
        case ["top"], ["start"], ["beginning"]: return .top
        case ["bottom"], ["end"]: return .bottom
        default: return match(target, said) >= 0.3 ? self : .notUnderstood
        }
    }
}

private let instructions = """
You turn one short spoken command for a pen editor of a formal specification into one action. \
The document has sections (headings such as "Notation" or "Rules (ctx)") and named rules (such as \
"el-trans" or "sub-comp", often heard as "el trans" or "sub comp"). Choose: goToSection for a section \
("go to notation", "conventions"); goToRule for a rule ("rule el trans", "show me sub comp"); goToLine \
for a line number ("line four thirty" is 430); find for anything else to look for ("where is the setoid \
model"); nextSection, previousSection; top or bottom for the start or end of the \
document ("go to the end"); selectTool to pick pen, eraser, lasso, move or revert; \
recognise to turn the handwriting into text ("recognise", "convert my ink"); undo; clearInk to throw the \
ink away; lineNumbers to show or hide line numbers; sectionsPanel to show or hide the list of sections ("sections", "hide sections"). \
Copy what names the target as it was said. If the command is none of these, choose notUnderstood.
"""

/// A step of the voice loop, timed, on the console.
private let clock = ContinuousClock.now
func log(_ s: String) {
    #if DEBUG
    print("voice \(clock.duration(to: .now)): \(s)")
    #endif
}

/// Speech recognition while the squeeze is held.
@MainActor
final class Listener {
    private let recognizer = SFSpeechRecognizer() ?? SFSpeechRecognizer(locale: Locale(identifier: "en-US"))
    private let engine = AVAudioEngine()
    private var request: SFSpeechAudioBufferRecognitionRequest?
    private var task: SFSpeechRecognitionTask?
    private var heard = ""
    private var over = false
    private var waiting: CheckedContinuation<String, Never>?

    static func allowed() async -> Bool {
        let speech = await withCheckedContinuation { done in
            SFSpeechRecognizer.requestAuthorization { done.resume(returning: $0 == .authorized) }
        }
        guard speech else { return false }
        return await AVAudioApplication.requestRecordPermission()
    }

    func start(vocabulary: [String], hearing: @escaping (String) -> Void) throws {
        guard let recognizer, recognizer.isAvailable else { throw CocoaError(.featureUnsupported) }
        let session = AVAudioSession.sharedInstance()
        try session.setCategory(.playAndRecord, mode: .measurement, options: [.duckOthers, .defaultToSpeaker])
        try session.setActive(true, options: .notifyOthersOnDeactivation)
        let request = SFSpeechAudioBufferRecognitionRequest()
        request.shouldReportPartialResults = true
        request.requiresOnDeviceRecognition = recognizer.supportsOnDeviceRecognition
        request.contextualStrings = vocabulary
        self.request = request
        heard = ""
        over = false
        let input = engine.inputNode
        input.removeTap(onBus: 0)
        input.installTap(onBus: 0, bufferSize: 1024, format: input.outputFormat(forBus: 0)) { buffer, _ in request.append(buffer) }
        engine.prepare()
        try engine.start()
        task = recognizer.recognitionTask(with: request) { [weak self] result, error in
            let text = result?.bestTranscription.formattedString, final = result?.isFinal == true || error != nil
            Task { @MainActor in
                // What comes once this listening is over (stopped, or another
                // begun) is ignored: it would show listening again.
                guard let self, self.request === request else { return }
                if let text {
                    self.heard = text
                    hearing(text)
                }
                if final { self.end() }
            }
        }
    }

    /// Stop listening: what was said, once the recogniser has heard the end
    /// of it (or after a moment, if it never says so).
    func finish() async -> String {
        engine.stop()
        engine.inputNode.removeTap(onBus: 0)
        request?.endAudio()
        if over { return heard }
        return await withCheckedContinuation { done in
            waiting = done
            Task { @MainActor in
                try? await Task.sleep(for: .seconds(1.5))
                self.end()
            }
        }
    }

    private func end() {
        over = true
        task?.cancel()
        task = nil
        request = nil
        try? AVAudioSession.sharedInstance().setActive(false, options: .notifyOthersOnDeactivation)
        if let waiting {
            self.waiting = nil
            waiting.resume(returning: heard)
        }
    }
}

/// The voice loop: listen while held, then understand, then act.
@MainActor
final class Voice: ObservableObject {
    enum State: Equatable {
        case idle
        case listening(String)
        case thinking(String)
        case told(String)
    }

    @Published private(set) var state: State = .idle
    let editor: Editor
    let relay: Relay
    /// Opens (a width) or closes (0) the sections panel.
    var setSectionsPanel: (Double) -> Void = { _ in }

    private let listener = Listener()
    private let speaker = AVSpeechSynthesizer()
    private var starting: Task<Bool, Never>?
    /// The language model's session for what is being said, loaded while it is said.
    private var session: LanguageModelSession?

    init(editor: Editor, relay: Relay) {
        self.editor = editor
        self.relay = relay
    }

    /// The squeeze is held: start listening.
    func begin() {
        log("begin")
        if case .available = SystemLanguageModel.default.availability {
            session = LanguageModelSession(instructions: instructions)
            session?.prewarm()
        }
        starting = Task {
            guard await Listener.allowed() else {
                tell("Voice needs the microphone and speech recognition, in Settings.")
                return false
            }
            let vocabulary = editor.sections.map(\.title) + ruleNames(of: editor.lines).map { $0.name.replacingOccurrences(of: "-", with: " ") }
            do {
                try listener.start(vocabulary: vocabulary) { self.state = .listening($0) }
                state = .listening("")
                return true
            } catch {
                tell("Speech recognition is not available.")
                return false
            }
        }
    }

    /// The squeeze is let go: act on what was said.
    func end() {
        Task {
            guard await starting?.value == true else { return }
            log("end")
            let said = await listener.finish()
            log("heard: \(said)")
            guard !said.trimmingCharacters(in: .whitespaces).isEmpty else {
                state = .idle
                return
            }
            state = .thinking(said)
            await perform(await understand(said), said: said)
        }
    }

    #if DEBUG
    /// Act on words as if they were said (for the simulator, which has no squeeze).
    func act(on said: String) {
        Task {
            state = .thinking(said)
            await perform(await understand(said), said: said)
        }
    }
    #endif

    /// The command said, as the language model reads it. Where the model
    /// cannot help (not on this iPad, a refusal: its guardrails take some rule
    /// names for something else, or no answer within a few seconds), all that
    /// was said is looked for in the text.
    private func understand(_ said: String) async -> Command {
        let fallback = Command.goTo(.anything, said)
        guard case .available = SystemLanguageModel.default.availability else { return fallback }
        let session = self.session ?? LanguageModelSession(instructions: instructions)
        self.session = nil
        // Whichever comes first, the answer or the time limit: a task group
        // would wait for the model even once cancelled, and it may not stop.
        return await withCheckedContinuation { done in
            var answered = false
            func answer(_ c: Command) {
                guard !answered else { return }
                answered = true
                done.resume(returning: c)
            }
            Task { @MainActor in
                let reply = try? await session.respond(to: said, generating: VoiceCommand.self,
                                                       options: GenerationOptions(temperature: 0))
                log("model: \(reply.map { "\($0.content)" } ?? "no answer")")
                answer(reply.map { Command($0.content).checked(against: said) } ?? fallback)
            }
            Task { @MainActor in
                try? await Task.sleep(for: .seconds(4))
                if !answered { log("model: out of time") }
                answer(fallback)
            }
        }
    }

    private func perform(_ command: Command, said: String) async {
        log("perform: \(command)")
        switch command {
        case .goTo(let kind, let target):
            let name = target.isEmpty ? said : target
            if let found = find(name, in: editor.lines, kind: kind) { editor.jump(toRow: found.row) } else { return tell("I couldn't find \(name).") }
        case .line(let n):
            guard editor.lines.indices.contains(n - 1) else { return tell("There is no line \(n).") }
            editor.jump(toRow: n - 1)
        case .nextSection, .previousSection:
            let at = editor.currentSection ?? -1, k = command == .nextSection ? at + 1 : at - 1
            guard editor.sections.indices.contains(k) else { return tell("There is no \(command == .nextSection ? "next" : "previous") section.") }
            editor.jump(to: editor.sections[k])
        case .top: editor.jump(toRow: 0)
        case .bottom: editor.jump(toRow: max(0, editor.lines.count - 1))
        case .tool(let t): editor.tool = t
        case .recognise: await editor.recognise(with: relay)
        case .undo: await editor.undo(with: relay)
        case .clearInk: editor.clear()
        case .lineNumbers(let on): editor.lineNumbers = on
        case .sections(let on): setSectionsPanel(on ? 300 : 0)
        case .notUnderstood: return tell("Sorry, I didn't understand: \(said).")
        }
        state = .idle
    }

    /// A failure: shown, and said aloud.
    private func tell(_ message: String) {
        state = .told(message)
        speaker.speak(AVSpeechUtterance(string: message))
        Task {
            try? await Task.sleep(for: .seconds(3))
            if state == .told(message) { state = .idle }
        }
    }
}

/// What voice is doing, in a bubble at the top of the page.
struct VoiceBubble: View {
    @ObservedObject var voice: Voice

    var body: some View {
        let shown: (icon: String, text: String)? = switch voice.state {
        case .idle: nil
        case .listening(let s): ("waveform", s.isEmpty ? "Listening…" : s)
        case .thinking(let s): ("ellipsis.bubble", s)
        case .told(let s): ("exclamationmark.bubble", s)
        }
        if let shown {
            let (icon, text) = shown
            HStack(spacing: 8) {
                Image(systemName: icon).symbolEffect(.variableColor, isActive: voice.state.isListening)
                Text(text).lineLimit(2)
            }
            .font(.callout)
            .padding(.horizontal, 14)
            .padding(.vertical, 8)
            .background(.regularMaterial, in: Capsule())
            .shadow(radius: 6, y: 2)
            .padding(.top, 8)
            .transition(.opacity.combined(with: .move(edge: .top)))
        }
    }
}

extension Voice.State {
    var isListening: Bool { if case .listening = self { true } else { false } }
}
