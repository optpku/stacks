/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Unramified.LocalStructure
import StacksCheckRecall

@[expose] public section

/-!
# Proposition 10.144.4

@stack 00UE
-/

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

/- Domain triage:
* primary domain: local étaleness and standard étale neighborhoods of finitely presented
  commutative algebras;
* sampled declarations: `IsEtaleAt`, `IsStandardEtale`, `IsStandardEtale.of_isLocalizationAway`,
  and `IsEtaleAt.exists_isStandardEtale`;
* source-facing layer: the existence of a standard étale basic-open neighborhood of an étale
  point;
* core/canonical layer: `IsEtaleAt.exists_isStandardEtale`;
* bridge/view layer: `StandardEtalePresentation`, which presents `IsStandardEtale` by explicit
  polynomial data.

Primitive-vs-derived split:
* primitive data: a prime `Q : Ideal S` with `[Q.IsPrime]`, finite presentation of `S` over `R`,
  and local étaleness `[IsEtaleAt R Q]`;
* derived API: the witness `f ∉ Q` and the induced `IsStandardEtale R (Localization.Away f)`.
-/

/- Proposition 10.144.4: if `Q ⊂ S` is a prime ideal and `R → S` is étale at `Q`, then there
exists `f ∈ S \ Q` such that the localized `R`-algebra `Localization.Away f` is standard étale
over `R`. -/
@[stacks 00UE]
#check @IsEtaleAt.exists_isStandardEtale

end Algebra
