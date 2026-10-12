/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Remark_60_24_12_Perfectness
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineCoefficients SheafOfModules

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {IA : Ideal A} (γA : DividedPowers IA)
variable (I : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
variable (s : Spec (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))

include x₀ in
/-- Nilpotence of `p` in `A / I` implies local nilpotence of `p` on a scheme over
the closed subscheme `V(I) ⊆ Spec(A)`. -/
theorem p_nilpotent_of_ideal_quotient (hI : specIdealEqOfIdealTop IA I)
    (hpI : IsNilpotent (Ideal.Quotient.mk IA (p : A))) :
    ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)) :=
  sorry

variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc X x₀)
variable [SectionsCoherent I γS hc x₀ F] [CrisModuleSheaf.IsCrystal F]

/-- Remark 60.24.13 (Complete perfectness): if `p` is prime, `(A, I, γ)` is a
divided-power ring with `A` `p`-adically complete and `p` nilpotent in `A / I`,
`S = Spec(A)`, `S₀ = V(I)`, `X` is proper and smooth over `S₀`, and `F` is a
crystal in finite locally free quasi-coherent `𝒪_{X/S}`-modules, then
`RΓ(Cris(X/S), F)` is a perfect object of `D(A)`. -/
@[stacks 07MY]
theorem derivedGlobalSections_isPerfect_of_isAdicComplete
    (hI : specIdealEqOfIdealTop IA I) (hγ : specDividedPowersEq IA γA I γS)
    (hpI : IsNilpotent (Ideal.Quotient.mk IA (p : A)))
    [IsAdicComplete (Ideal.span {(p : A)}) A]
    [IsProper x₀] [Smooth x₀]
    [HasWeakSheafify (smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀
      (p_nilpotent_of_ideal_quotient I x₀ hI hpI)) AddCommGrpCat.{u}]
    [(smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀
      (p_nilpotent_of_ideal_quotient I x₀ hI hpI)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U : smallCrystallineSite (Spec (.of A)) I γS hc X x₀,
      HasWeakSheafify ((smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀
        (p_nilpotent_of_ideal_quotient I x₀ hI hpI)).over U) AddCommGrpCat.{u}]
    [∀ U : smallCrystallineSite (Spec (.of A)) I γS hc X x₀,
      ((smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀
        (p_nilpotent_of_ideal_quotient I x₀ hI hpI)).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    [IsCrystalInFiniteLocallyFreeModules
      (ofCrystal I γS hc x₀ F p s (p_nilpotent_of_ideal_quotient I x₀ hI hpI))]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1}
      (liftedRingedSite I γS hc x₀ p s (p_nilpotent_of_ideal_quotient I x₀ hI hpI)))] :
    (derivedGlobalSections I γS hc x₀ s
      (p_nilpotent_of_ideal_quotient I x₀ hI hpI) F).IsPerfect :=
  sorry

end AlgebraicGeometry.Scheme.Crystalline
