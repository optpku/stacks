module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.AdicCompletion.Basic
public import stacks_project.Chap69.Lemma_69_22_4_System

/-!
# Comparison from I-adic completion of cohomology to the quotient tower

The maps `H^p(X, F) / I^n H^p(X, F) ⟶ H^p(X, F / I^n F)` assemble to a morphism
from the I-adic completion of `H^p(X, F)` to the inverse limit of the quotient
cohomology system.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology
open CategoryTheory CategoryTheory.ConcreteCategory CategoryTheory.Limits Opposite

noncomputable section

universe u

variable {A : Type u} [CommRing A]
variable {X : AlgebraicSpace (Spec (CommRingCat.of A))}

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

/-- The ideal power `I^n` annihilates the image of `H^p(X, F)` in
`H^p(X, F / I^n F)`, so it is contained in the kernel of
`toQuotientCohomology`. -/
theorem pow_smul_le_ker_toQuotientCohomology (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    I ^ n • (⊤ : Submodule A
        (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p)) ≤
      LinearMap.ker (toQuotientCohomology I f F p n).hom :=
  sorry

/-- The descended comparison `H^p(X, F) / I^n H^p(X, F) ⟶ H^p(X, F / I^n F)`. -/
def toQuotientModPow (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    ModuleCat.of A
      (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p ⧸
        I ^ n • (⊤ : Submodule A
          (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p))) ⟶
      quotientCohomology I f F p n :=
  ConcreteCategory.ofHom
    ((I ^ n • (⊤ : Submodule A
        (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p))).liftQ
      (toQuotientCohomology I f F p n).hom
      (pow_smul_le_ker_toQuotientCohomology I f F p n))

/-- Composing `toQuotientModPow` with the quotient map recovers
`toQuotientCohomology`. -/
theorem toQuotientModPow_comp_mkQ (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    (toQuotientModPow I f F p n).hom ∘ₗ
        Submodule.mkQ
          (I ^ n • (⊤ : Submodule A
            (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p))) =
      (toQuotientCohomology I f F p n).hom :=
  sorry

/-- The descended comparisons are natural with respect to the adic quotient
transitions and the cohomology tower. -/
theorem toQuotientModPow_natural (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    ModuleCat.ofHom
        (AdicCompletion.transitionMap I
          (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p) h) ≫
        toQuotientModPow I f F p m =
      toQuotientModPow I f F p n ≫ (quotientSystem I f F p).transitionMap h :=
  sorry

/-- The induced map from the I-adic completion of `H^p(X, F)` to the inverse
limit of `H^p(X, F / I^n F)`. -/
def limitComparison (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    ModuleCat.of A
      (AdicCompletion I
        (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p)) ⟶
      limit (quotientSystem I f F p) :=
  limit.lift (quotientSystem I f F p)
    { pt := ModuleCat.of A
        (AdicCompletion I
          (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p))
      π :=
        { app := fun n ↦
            ConcreteCategory.ofHom
              ((toQuotientModPow I f F p n.unop).hom ∘ₗ
                AdicCompletion.eval I
                  (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p)
                  n.unop)
          naturality := fun _ _ _ ↦ sorry } }

/-- Projecting `limitComparison` to stage `n` is evaluation on the completion
followed by `toQuotientModPow`. -/
theorem limitComparison_comp_π (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    limitComparison I f F p ≫ limit.π (quotientSystem I f F p) (op n) =
      ModuleCat.ofHom
        ((toQuotientModPow I f F p n).hom ∘ₗ
          AdicCompletion.eval I
            (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p) n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology
