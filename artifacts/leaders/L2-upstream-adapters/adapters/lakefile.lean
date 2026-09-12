import Lake
open Lake DSL

/-
Isolated adapter package for the pinned Frenzymath snapshot (M2).

The upstream projects are consumed **in place** as Lake path requirements: no
upstream source is copied into this package and no pin is flattened.  The
snapshot keeps its own `lean-toolchain` (leanprover/lean4:v4.32.1) and its own
mathlib pin (520045ab14e26149ee970e2e617ca04b09bde5d6); this package adopts the
same pins because it must elaborate upstream oleans, and records that fact here
instead of rewriting the upstream manifests.
-/

package UpstreamAdapters where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "520045ab14e26149ee970e2e617ca04b09bde5d6"

require Shared from "../third_party/frenzymath/Poincare-Conjecture/shared"
require DoCarmoLib from "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/DoCarmo"
require MorganTianLib from "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/MorganTian"
require Topping from "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/Topping"
require PetersenLib from "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/Petersen"
require HatcherLib from "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/Hatcher"
require KleinerLott from "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/KleinerLott"
require ChowKnopf from "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/ChowKnopf"

-- Round 4: the four remaining inventoried packages are compile-checked at the
-- same pin.  They are required here (so `lake build <target>` can build them in
-- this workspace) but are **not** imported by this package's modules, so their
-- Lean environments never mix with the adapter's and the adapter audit is
-- unaffected.
require LeeLib from "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/LeeRiemannian"
require EvansLib from "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/Evans"
require HanLinLectureNotes from "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/HanLinLectureNotes"
require GilbargTrudinger from "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/GilbargTrudinger"

@[default_target]
lean_lib UpstreamAdapters where
  roots := #[`UpstreamAdapters]
  globs := #[.andSubmodules `UpstreamAdapters]

/-- PetersenLib cannot share a Lean environment with `Shared`: both call
`register_simp_attr metric_simp`, so a module importing both fails with
"environment already contains 'Parser.Attr.metric_simp'".  Petersen adapters
therefore live in their own library and are never imported together with the
Shared-based family. -/
lean_lib UpstreamAdaptersPetersen where
  roots := #[`UpstreamAdaptersPetersen]
  globs := #[.andSubmodules `UpstreamAdaptersPetersen]
