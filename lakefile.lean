import Lake
open Lake DSL

package optisat where
  version := v!"0.1.0"
  keywords := #["equality-saturation", "e-graph", "verification"]
  leanOptions := #[⟨`pp.unicode.fun, true⟩, ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib LambdaSat where

lean_lib Tests where
  globs := #[.submodules `Tests]

lean_exe «integration-tests» where
  root := `Tests.IntegrationTests
