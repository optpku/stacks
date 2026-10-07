module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.AdicCompletion.Basic
public import stacks_project.Chap30.Lemma_30_20_4_Quotient

/-!
# Comparison from I-adic completion of cohomology to the quotient tower

The maps `Hom.cohomology f F p ⧸ I ^ n • ⊤ ⟶ cohomology I f F p n` assemble to
a morphism from the I-adic completion of `Hom.cohomology f F p` to the inverse
limit of the quotient cohomology tower.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ConcreteCategory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.Quotient

variable {A : Type u} [CommRing A]
variable {X : Scheme.{u}}
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- The ideal power `I ^ n` annihilates the image of `Hom.cohomology f F p` in
`cohomology I f F p n`, so it is contained in the kernel of `toQuotient`. -/
theorem pow_smul_le_ker_toQuotient (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    I ^ n • (⊤ : Submodule A (Hom.cohomology f F p)) ≤
      LinearMap.ker (toQuotient I f F p n).hom :=
  sorry

/-- The descended comparison
`Hom.cohomology f F p ⧸ I ^ n • ⊤ ⟶ cohomology I f F p n`. -/
def toQuotientModPow (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    ModuleCat.of A
      (Hom.cohomology f F p ⧸ I ^ n • (⊤ : Submodule A (Hom.cohomology f F p))) ⟶
      cohomology I f F p n :=
  ConcreteCategory.ofHom
    ((I ^ n • (⊤ : Submodule A (Hom.cohomology f F p))).liftQ
      ((toQuotient I f F p n).hom :
        Hom.cohomology f F p →ₗ[A] cohomology I f F p n)
      (pow_smul_le_ker_toQuotient I f F p n))

/-- Composing `toQuotientModPow` with the quotient map recovers `toQuotient`. -/
theorem toQuotientModPow_comp_mkQ (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    (toQuotientModPow I f F p n).hom ∘ₗ
        Submodule.mkQ (I ^ n • (⊤ : Submodule A (Hom.cohomology f F p))) =
      (toQuotient I f F p n).hom :=
  sorry

/-- The descended comparisons are natural with respect to the adic quotient
transitions and the cohomology tower. -/
theorem toQuotientModPow_natural (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    ModuleCat.ofHom (AdicCompletion.transitionMap I (Hom.cohomology f F p) h) ≫
        toQuotientModPow I f F p m =
      toQuotientModPow I f F p n ≫ transition I f F p h :=
  sorry

/-- The induced map from the I-adic completion of `Hom.cohomology f F p` to the
inverse limit of `n ↦ cohomology I f F p n`. -/
def limitComparison (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p : ℕ) :
    ModuleCat.of A (AdicCompletion I (Hom.cohomology f F p)) ⟶
      limit (tower I f F p) :=
  limit.lift (tower I f F p)
    { pt := ModuleCat.of A (AdicCompletion I (Hom.cohomology f F p))
      π :=
        { app := fun n ↦
            ConcreteCategory.ofHom
              (((toQuotientModPow I f F p n.unop).hom ∘ₗ
                  AdicCompletion.eval I (Hom.cohomology f F p) n.unop) :
                AdicCompletion I (Hom.cohomology f F p) →ₗ[A]
                  cohomology I f F p n.unop)
          naturality := fun _ _ _ ↦ sorry } }

/-- Projecting `limitComparison` to stage `n` is evaluation on the completion
followed by `toQuotientModPow`. -/
theorem limitComparison_comp_π (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    limitComparison I f F p ≫ limit.π (tower I f F p) (op n) =
      ConcreteCategory.ofHom
        (((toQuotientModPow I f F p n).hom ∘ₗ
            AdicCompletion.eval I (Hom.cohomology f F p) n) :
          AdicCompletion I (Hom.cohomology f F p) →ₗ[A]
            cohomology I f F p n) :=
  sorry

end AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.Quotient
