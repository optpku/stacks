module

public import ReasLib.RingTheory.DividedPowers.DeRham.Cosimplicial
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

@[expose] public section

open CategoryTheory Opposite PresheafOfModules

noncomputable section

universe u

variable {A : Type u} [CommRing A]
variable (p : ℕ) [pPrime : Fact (Nat.Prime p)]
variable [baseLocal : Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (I : Ideal A) (γ : DividedPowers I)
variable {C : Type u} [CommRing C] [Algebra A C]
variable {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
variable (hπ : Function.Surjective π)
variable (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable (J : (n : ℕ) → Ideal (MvPolynomial.TensorPower.carrier A ι n))
variable (hJ : ∀ n, J n = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
variable (hIJ : ∀ n, Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ J n)
variable (E : (n : ℕ) →
    DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) (J n) (hIJ n))
variable (hE : ∀ n,
    DividedPowerEnvelope.IsUniversal γ
      (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) (hIJ n) (E n))
variable (γbar : (n : ℕ) → DividedPowers (Crystalline.dnIdeal p I γ J hIJ E n))
variable (hγbar : ∀ n, DividedPowers.IsDPMorphism (E n).D.dividedPowers (γbar n)
    (algebraMap (E n).D (AdicCompletion (Ideal.span {(p : (E n).D)}) (E n).D)))
variable (i : ℕ)

namespace Crystalline

/-- The exterior powers of the completed relative divided-power differential diagram. -/
def omegaExteriorDStar :
    PresheafOfModules.{u} (moduleRingPresheaf (dStar p I γ π J hJ hIJ E hE)) :=
  ExteriorPower.presheaf (cosimplicialCommRing (dStar p I γ π J hJ hIJ E hE))
    (omegaDStar p I γ π J hJ hIJ E hE γbar hγbar) i

/-- The principal-adic completion of an exterior power of completed differentials
in a single degree. -/
def omegaPowerModule (n : ℕ) : ModuleCat.{u} (dn p I γ J hIJ E n) :=
  ModuleCat.of (dn p I γ J hIJ E n)
    (AdicCompletion (Ideal.span {(p : dn p I γ J hIJ E n)})
      (ModuleCat.exteriorPower (R := dn p I γ J hIJ E n)
        ((omegaDStar p I γ π J hJ hIJ E hE γbar hγbar).obj
          (op (op (SimplexCategory.mk n)))) i))

/-- The completed exterior powers of the completed relative divided-power
differential diagram. -/
def omegaPowerDStar :
    PresheafOfModules.{u} (moduleRingPresheaf (dStar p I γ π J hJ hIJ E hE)) :=
  CosimplicialModule.adicCompletion (primeIdeals p I γ π J hJ hIJ E hE)
    (omegaExteriorDStar p I γ π J hJ hIJ E hE γbar hγbar i)

/-- Each stage of the completed exterior-power diagram is the principal-adic
completion of the exterior power of the completed differential module. -/
theorem omegaPowerDStar_obj (n : ℕ) :
    (omegaPowerDStar p I γ π J hJ hIJ E hE γbar hγbar i).obj
        (op (op (SimplexCategory.mk n))) =
      ModuleCat.of (dn p I γ J hIJ E n)
        (AdicCompletion (Ideal.span {(p : dn p I γ J hIJ E n)})
          (ModuleCat.exteriorPower (R := dn p I γ J hIJ E n)
            ((omegaDStar p I γ π J hJ hIJ E hE γbar hγbar).obj
              (op (op (SimplexCategory.mk n)))) i)) := rfl

variable (M : PresheafOfModules.{u} (moduleRingPresheaf (dStar p I γ π J hJ hIJ E hE)))

/-- The completed tensor product of a cosimplicial module with the completed
exterior powers of completed relative divided-power differentials. -/
def omegaPowerTensor :
    PresheafOfModules.{u} (moduleRingPresheaf (dStar p I γ π J hJ hIJ E hE)) :=
  CosimplicialModule.adicCompletion (primeIdeals p I γ π J hJ hIJ E hE)
    (Monoidal.tensorObj M (omegaPowerDStar p I γ π J hJ hIJ E hE γbar hγbar i))

/-- Each stage of the completed tensor diagram is the principal-adic completion
of the tensor product with the completed exterior-power module. -/
theorem omegaPowerTensor_obj (n : ℕ) :
    (omegaPowerTensor p I γ π J hJ hIJ E hE γbar hγbar i M).obj
        (op (op (SimplexCategory.mk n))) =
      ModuleCat.of (dn p I γ J hIJ E n)
        (AdicCompletion (Ideal.span {(p : dn p I γ J hIJ E n)})
          (MonoidalCategory.tensorObj (C := ModuleCat (dn p I γ J hIJ E n))
            (M.obj (op (op (SimplexCategory.mk n))))
            (omegaPowerModule p I γ π J hJ hIJ E hE γbar hγbar i n))) := rfl

end Crystalline

include hπ hIC hpnil baseLocal pPrime in
/-- The completed tensor product of any cosimplicial module with a positive
completed exterior power of crystalline differentials is linearly homotopic to zero. -/
theorem crystallineOmegaPowerTensor_homotopic_zero
    (M : PresheafOfModules.{u}
      (moduleRingPresheaf (Crystalline.dStar p I γ π J hJ hIJ E hE)))
    (i : ℕ) (hi : 0 < i) :
    CosimplicialModule.Homotopic
      (𝟙 (Crystalline.omegaPowerTensor p I γ π J hJ hIJ E hE γbar hγbar i M))
      (0 :
        Crystalline.omegaPowerTensor p I γ π J hJ hIJ E hE γbar hγbar i M ⟶
          Crystalline.omegaPowerTensor p I γ π J hJ hIJ E hE γbar hγbar i M) := sorry
