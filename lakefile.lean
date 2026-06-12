import Lake
open Lake DSL

package LeanLambda where
  srcDir := "."

require "leanprover" / "verso-slides" @ git "v4.31.0-rc1"
require "leanprover-community" / "mathlib"

@[default_target]
lean_lib LeanLambda where
  roots := #[`LeanLambda]

lean_lib LeanLambdaSlides where
  roots := #[`LeanLambdaSlides]

lean_lib LeanLambdaBook where
  roots := #[`LeanLambdaBook]

lean_exe «generate-slides» where
  root := `LeanLambdaSlides.Main

lean_exe «generate-book» where
  root := `LeanLambdaBook.Main
