module Data.Interpolation

public export
Interpolation a => Interpolation (List a) where
  interpolate list = "[" ++ go list ++ "]"
    where
      go : List a -> String
      go [] = ""
      go [x] = interpolate x
      go (x :: y :: zs) = interpolate x ++ ", " ++ go (y :: zs)

public export
Interpolation a => Interpolation (SnocList a) where
  interpolate list = "[<" ++ go list ++ "]"
    where
      go : SnocList a -> String
      go [<] = ""
      go [< x] = interpolate x
      go (zs :< y :< x) = go (zs :< y) ++ ", " ++ interpolate x
