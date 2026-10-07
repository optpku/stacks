import stacks_project.Chap51.Lemma_51_22_4_Twist

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace AdicSectionConstructionTest

universe u

-- This example checks the implementation, not the deferred tmul specification.
example {A : Type u} [CommRing A] (I : Ideal A) (q : ℕ)
    (a : I) (b : ↥(I ^ q)) :
    ((IsBlowup.idealPowerProduct I q).hom (a ⊗ₜ[A] b) : A) =
      (a : A) * (b : A) := rfl

-- A genuine quotient-descent equation follows from Mathlib's epiDesc law.
example {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (q : ℕ) :
    (Scheme.Modules.affineBaseModuleAssociatedFunctor A p).map
        (IsBlowup.idealPowerProduct I q) ≫
      IsBlowup.idealPowerToExceptionalPower I p (q + 1) =
        IsBlowup.exceptionalPowerProductMap I p q
          (IsBlowup.idealPowerToExceptionalPower I p q) :=
  Abelian.comp_epiDesc _ _ _

end AdicSectionConstructionTest
