/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.BaseChange

/-!
# Base change of an invariant pre-relation

This chapter-facing module exposes the canonical base-change API to existing
chapter consumers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U X X' : Over B}
variable (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) (f : X' ⟶ X)

#check (baseChange P hφ f : PreRelation (pullback φ f))
#check (baseChange_t P hφ f :
  (P.baseChange hφ f).t = (P.cofork hφ).baseChangeLeft f)
#check (baseChange_s P hφ f :
  (P.baseChange hφ f).s = (P.cofork hφ).baseChangeRight f)
#check (baseChange_hom P hφ f :
  (P.baseChange hφ f).hom =
    prod.lift ((P.cofork hφ).baseChangeLeft f) ((P.cofork hφ).baseChangeRight f))
#check (baseChange_left P hφ f :
  (P.baseChange hφ f).left = pullback (P.t ≫ φ) f)

variable [Mono P.hom]

#check (monoHom_baseChange P hφ f : Mono (P.baseChange hφ f).hom)

variable (hP : P.IsPreEquivalence)

#check (IsPreEquivalence.baseChange hP hφ f :
  (P.baseChange hφ f).IsPreEquivalence)

variable [IsEquivalenceRelation P.t P.s]

#check (isEquivalenceRelation_baseChange P hφ f :
  IsEquivalenceRelation (P.baseChange hφ f).t (P.baseChange hφ f).s)

end AlgebraicGeometry.AlgebraicSpace.PreRelation
