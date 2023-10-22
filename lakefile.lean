import Lake
open Lake DSL

package «symmetric_project» {
  moreLinkArgs := #["-L./lake-packages/LeanInfer/build/lib", "-lonnxruntime", "-lctranslate2"]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
require LeanInfer from git "https://github.com/lean-dojo/LeanInfer" @ "improve-backend"

@[default_target]
lean_lib «SymmetricProject» {
  -- add any library configuration options here
}
