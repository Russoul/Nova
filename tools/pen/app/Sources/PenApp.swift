import SwiftUI

@main
struct PenApp: App {
    var body: some Scene {
        WindowGroup { ContentView() }
    }
}

struct ContentView: View {
    @StateObject private var relay = Relay()
    @AppStorage("relay") private var address = "http://127.0.0.1:8765"

    var body: some View {
        VStack(spacing: 0) {
            HStack {
                TextField("Relay address", text: $address)
                    .textFieldStyle(.roundedBorder)
                    .textInputAutocapitalization(.never)
                    .autocorrectionDisabled()
                    .frame(maxWidth: 420)
                    .onSubmit { relay.connect(to: address) }
                Button("Connect") { relay.connect(to: address) }
                Spacer()
                Text(relay.status).font(.caption).foregroundStyle(.secondary)
            }
            .padding(8)
            Divider()
            PageRepresentable(lines: relay.lines, version: relay.version)
        }
        .onAppear { relay.connect(to: address) }
    }
}

/// The UIKit page in SwiftUI; it redraws only when the file's version changes.
struct PageRepresentable: UIViewRepresentable {
    let lines: [String]
    let version: String

    final class Coordinator {
        var shown: String?
    }

    func makeCoordinator() -> Coordinator { Coordinator() }

    func makeUIView(context: Context) -> PageScroll { PageScroll(frame: .zero) }

    func updateUIView(_ scroll: PageScroll, context: Context) {
        guard context.coordinator.shown != version else { return }
        context.coordinator.shown = version
        scroll.show(Layout(rows: lines.map(Array.init), glyphs: .bundled))
    }
}
