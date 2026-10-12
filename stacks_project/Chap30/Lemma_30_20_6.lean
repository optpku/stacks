/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import stacks_project.Chap30.Lemma_30_20_6_Comparison

/-!
# Spell-out of the theorem on formal functions

If the Noetherian base ring `A` is `I`-adically complete, the comparison
`H^p(X, F) ⟶ lim_n H^p(X, F / I^n F)` is already an isomorphism, so
completion on the left-hand side is unnecessary.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace IdealPowerCohomology
namespace Quotient

variable {A : Type u} [CommRing A]
variable {X : Scheme.{u}}
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- Lemma 30.20.6: if `A` is Noetherian and `I`-adically complete, `f : X ⟶ Spec(A)`
is a proper morphism, and `F` is a coherent sheaf on `X`, then the canonical
comparison `H^p(X, F) ⟶ lim_n H^p(X, F / I^n F)` is an isomorphism of
`A`-modules for every `p : ℕ`. -/
@[stacks 087U, instance]
instance isIso_toLimit [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (p : ℕ) :
    IsIso (toLimit I f F p) :=
  sorry

end Quotient
end IdealPowerCohomology
end AlgebraicGeometry.Scheme.Hom
