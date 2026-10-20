/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Unramified.LocalStructure
import StacksCheckRecall

@[expose] public section

/-!
# Proposition 10.152.1

@stack 0395
-/

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

/- Domain triage:
* primary domain: local structure of finite-type unramified algebra maps via standard étale
  neighborhoods and surjections onto basic-open localizations;
* sampled declarations: `IsUnramifiedAt`, `HasStandardEtaleSurjectionOn`,
  `IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`, and `IsEtaleAt.exists_isStandardEtale`;
* source-facing layer: the existence of a standard étale `R`-algebra surjecting onto
  `S[1 / f]` near an unramified prime;
* core/canonical layer: `IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`;
* bridge/view layer: `HasStandardEtaleSurjectionOn`, which packages the surjective map from a
  standard étale algebra to the localization.

Primitive-vs-derived split:
* primitive data: a prime `Q : Ideal S` with `[Q.IsPrime]`, finite type of `S` over `R`, and the
  local owner `[IsUnramifiedAt R Q]`;
* derived API: a witness `f ∉ Q` and the resulting `HasStandardEtaleSurjectionOn R f`.
-/

/- Proposition 10.152.1: if `Q ⊂ S` is a prime ideal and `R → S` is unramified at `Q`, then
there exists `f ∈ S \ Q` and a standard étale `R`-algebra surjecting onto the localization
`S[1 / f]`. This is exactly the canonical local-structure theorem
`IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`. -/
@[stacks 0395]
#check @IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn

end Algebra
