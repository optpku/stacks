module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Abelian
public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.DeltaOne.Relation
public import stacks_project.Chap60.Lemma_60_19_3_OmegaPower
import Mathlib.Tactic.CrossRefAttribute

open CategoryTheory PresheafOfModules
open scoped Simplicial

@[expose] public section

noncomputable section

universe u

variable {A : Type u} [CommRing A]
variable (p : ℕ) [Fact (Nat.Prime p)]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (I : Ideal A) (γ : DividedPowers I)
variable {C : Type u} [CommRing C] [Algebra A C]
variable {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
variable (hπ : Function.Surjective π)
variable (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable (J : (n : ℕ) → Ideal (tensorPowerCarrier A ι n))
variable (hJ : ∀ n, J n = RingHom.ker (tensorPowerAlgHom π n).toRingHom)
variable (hIJ : ∀ n, Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ J n)
variable (E : (n : ℕ) →
    DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) (J n) (hIJ n))
variable (hE : ∀ n,
    DividedPowerEnvelope.IsUniversal γ
      (algebraMap A (tensorPowerCarrier A ι n)) (hIJ n) (E n))
variable (γbar : (n : ℕ) →
    DividedPowers
      (crystallineDnIdeal p I γ π hπ n hIC hpnil (J n) (hJ n) (hIJ n) (E n) (hE n)))

/-- Lemma 60.19.3: with notation as in (60.17.0.4) and (60.17.0.5), for any
cosimplicial `D(*)`-module `M_*` and any `i > 0` the cosimplicial module with
stages `M_n ⊗^∧_{D(n)} Ω^i_{D(n)}` is homotopic to zero, where `Ω^i_{D(n)}` is
the `p`-adic completion of `∧^i Ω_{D(n)}`. -/
@[stacks 07LA]
theorem crystallineOmegaPowerTensor_homotopic_zero
    (M : PresheafOfModules.{u}
      (moduleRingPresheaf (crystallineDStar p I γ π hπ hIC hpnil J hJ hIJ E hE)))
    (i : ℕ) (hi : 0 < i) :
    CosimplicialObject.DeltaOneHomotopic
      (𝟙 (crystallineOmegaPowerTensor p I γ π hπ hIC hpnil J hJ hIJ E hE γbar i M))
      (0 :
        crystallineOmegaPowerTensor p I γ π hπ hIC hpnil J hJ hIJ E hE γbar i M ⟶
          crystallineOmegaPowerTensor p I γ π hπ hIC hpnil J hJ hIJ E hE γbar i M) :=
  sorry
