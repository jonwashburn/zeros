import Lake
open Lake DSL

package «riemann» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
  -- Build optimizations for performance
  buildType := BuildType.release
  -- Parallel compilation (uncomment and adjust for your CPU cores)
  moreLeanArgs := #["-j2", "-M", "6144"] -- limit threads and memory for stability
  -- Enable incremental compilation
  -- moreGlobalServerArgs := #["--worker-pool-size=8"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.13.0"

-- Local dependency on no-mathlib-core removed since it was moved to archive

lean_lib «rh» where
  -- Build a minimal, paper-relevant core to keep the active track green
  globs := #[
    .submodules `rh.Cert,
    .submodules `rh.Blockers,
    .submodules `rh.RS
  ]

-- Optional academic framework (not part of default target). Build with:
--   lake build af
lean_lib «af» where
  globs := #[
    .submodules `rh.academic_framework
  ]

-- Test library for verification and validation
lean_lib «test» where
  globs := #[.submodules `test]

@[default_target]
lean_exe «core» where
  root := `core.BuildCore
