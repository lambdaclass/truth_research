import Lake
open Lake DSL

package optisat where
  version := v!"0.1.0"
  keywords := #["equality-saturation", "e-graph", "verification"]
  leanOptions := #[⟨`pp.unicode.fun, true⟩, ⟨`relaxedAutoImplicit, false⟩]

require leanExtensions from git
  "https://github.com/lambdaclass/lean_extensions.git" @ "a78bc66074108f7f859bf99251c791e8b2cc2e36"

target axiomGuardPlugin : Dynlib := do
  let some lib ← findLeanLib? `LeanExtensions | error "could not find the `LeanExtensions` lean_lib"
  lib.shared.fetch

@[default_target]
lean_lib LambdaSat where
  plugins := #[axiomGuardPlugin]

lean_lib Tests where
  globs := #[.submodules `Tests]
  plugins := #[axiomGuardPlugin]

lean_exe «integration-tests» where
  root := `Tests.IntegrationTests
  plugins := #[axiomGuardPlugin]
