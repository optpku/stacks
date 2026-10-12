/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.AdicCompletion.Basic
public import stacks_project.Chap69.Lemma_69_22_4_System

/-!
# Spell-out of the theorem on formal functions

If the Noetherian base ring `A` is `I`-adically complete, the comparison
`H^p(X, F) ⟶ lim_n H^p(X, F / I^n F)` is already an isomorphism, so
completion on the left-hand side is unnecessary.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

variable {A : Type u} [CommRing A]
variable {X : AlgebraicSpace (Spec (CommRingCat.of A))}

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace IdealPowerCohomology

/-- The canonical comparison `H^p(X, F) ⟶ lim_n H^p(X, F / I^n F)` induced by
`toQuotientCohomology`. -/
def toLimit (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p ⟶
      limit (quotientSystem I f F p) :=
  limit.lift (quotientSystem I f F p)
    { pt := GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p
      π :=
        { app := fun n ↦ toQuotientCohomology I f F p n.unop
          naturality := fun _ _ _ ↦ sorry } }

/-- Projecting `toLimit` to stage `n` recovers `toQuotientCohomology`. -/
theorem toLimit_comp_π (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    toLimit I f F p ≫ limit.π (quotientSystem I f F p) (op n) =
      toQuotientCohomology I f F p n :=
  sorry

/-- Lemma 69.22.6: if `A` is Noetherian and `I`-adically complete, `f : X ⟶ Spec(A)`
is a proper morphism of algebraic spaces, and `F` is coherent on `X`, then the
canonical comparison `H^p(X, F) ⟶ lim_n H^p(X, F / I^n F)` is an isomorphism of
`A`-modules for every `p : ℕ`. -/
@[stacks 08B0]
instance isIso_toLimit [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
    (F : X.Modules) [F.IsCoherent]
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    IsIso (toLimit I f F p) :=
  sorry

end IdealPowerCohomology
end AlgebraicGeometry.AlgebraicSpace.Modules

