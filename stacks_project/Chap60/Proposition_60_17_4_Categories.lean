module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap60.Lemma_60_17_3_Pair
public import stacks_project.Chap60.Definition_60_11_1_ModuleProperties
public import stacks_project.Chap60.«60_23_2_1_Eval»

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf
open CrystallineConnectionPair

universe u

variable {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (I : Ideal A) (γ : DividedPowers I)
variable {C : Type u} [CommRing C] [Algebra A C]
variable {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
variable (hπ : Function.Surjective π)
variable (J : Ideal (MvPolynomial ι A))
variable (hJ : J = RingHom.ker π.toRingHom)
variable (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable (hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J)
variable (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
variable (hE : DividedPowerEnvelope.IsUniversal γ
  (algebraMap A (MvPolynomial ι A)) hIJ E)
variable (γbar : DividedPowers
  (Ideal.map (algebraMap E.D
    (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)) E.D.ideal))
variable {S : Scheme.{u}} {IS : S.IdealSheafData}
variable {γS : ∀ V : S.affineOpens, DividedPowers (IS.ideal V)}
variable {h_compatible :
    ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γS V).IsDPMorphism (γS (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ IS.subscheme}

namespace CrystallineModuleSheaf

/-- A crystal in locally quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)`. -/
class IsQuasiCoherentCrystal
    (F : CrisModuleSheaf S IS γS h_compatible X x₀) : Prop where
  /-- The crystal comparison-isomorphism property. -/
  isCrystal : CrisModuleSheaf.IsCrystal F
  /-- Local quasi-coherence of the underlying module sheaf. -/
  isLocallyQuasiCoherent : CrisModuleSheaf.IsLocallyQuasiCoherent F

/-- Crystals in quasi-coherent modules are crystals. -/
instance IsQuasiCoherentCrystal.toIsCrystal
    (F : CrisModuleSheaf S IS γS h_compatible X x₀)
    [h : IsQuasiCoherentCrystal F] : CrisModuleSheaf.IsCrystal F :=
  h.isCrystal

/-- Crystals in quasi-coherent modules are locally quasi-coherent. -/
instance IsQuasiCoherentCrystal.toIsLocallyQuasiCoherent
    (F : CrisModuleSheaf S IS γS h_compatible X x₀)
    [h : IsQuasiCoherentCrystal F] :
    CrisModuleSheaf.IsLocallyQuasiCoherent F :=
  h.isLocallyQuasiCoherent

/-- Characterization of crystals in quasi-coherent `𝒪_{X/S}`-modules. -/
theorem IsQuasiCoherentCrystal.iff
    (F : CrisModuleSheaf S IS γS h_compatible X x₀) :
    IsQuasiCoherentCrystal F ↔
      CrisModuleSheaf.IsCrystal F ∧ CrisModuleSheaf.IsLocallyQuasiCoherent F :=
  sorry

/-- The full subcategory of crystals in quasi-coherent `𝒪_{X/S}`-modules. -/
abbrev QuasiCoherentCrystal
    (S : Scheme.{u}) (IS : S.IdealSheafData)
    (γS : ∀ V : S.affineOpens, DividedPowers (IS.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γS V).IsDPMorphism (γS (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ IS.subscheme) :=
  ObjectProperty.FullSubcategory
    (fun F : CrisModuleSheaf S IS γS h_compatible X x₀ ↦ IsQuasiCoherentCrystal F)

end CrystallineModuleSheaf

namespace CrystallineConnectionPair

/-- Bundled pairs `(M, ∇)` of `p`-adically complete `D`-modules with completed
connections satisfying (07JB)–(07JE). -/
structure ConnectionPairCat
    {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I)
    {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
    (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial ι A))
    (hJ : J = RingHom.ker π.toRingHom)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
    (hpnil : IsNilpotent (p : C))
    (hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ
      (algebraMap A (MvPolynomial ι A)) hIJ E)
    (γbar : DividedPowers
      (Ideal.map (algebraMap E.D
        (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)) E.D.ideal)) where
  /-- The underlying `D`-module. -/
  M : Type u
  /-- Additive group structure on `M`. -/
  addCommGroup : AddCommGroup M
  /-- `D`-module structure on `M`. -/
  module : Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M
  /-- The completed connection pair on `M`. -/
  pair : CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M

/-- Bundle a completed connection pair as an object of the pair category. -/
noncomputable def ConnectionPairCat.of
    {M : Type u} [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M]
    (P : CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M) :
    ConnectionPairCat p I γ π hπ J hJ hIC hpnil hIJ E hE γbar :=
  { M := M
    addCommGroup := inferInstance
    module := inferInstance
    pair := P }

/-- The bundled object retains the supplied pair. -/
theorem ConnectionPairCat.of_pair
    {M : Type u} [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M]
    (P : CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M) :
    (ConnectionPairCat.of p I γ π hπ J hJ hIC hpnil hIJ E hE γbar P).pair = P :=
  sorry

/-- The category of completed connection pairs satisfying (07JB)–(07JE). -/
noncomputable instance connectionPairCatCategory :
    Category (ConnectionPairCat p I γ π hπ J hJ hIC hpnil hIJ E hE γbar) where
  Hom P Q :=
    @CrystallineConnectionPair.Hom A _ p _ _ I γ C _ _ ι π hπ J hJ hIC hpnil hIJ E hE
      γbar P.M Q.M P.addCommGroup Q.addCommGroup P.module Q.module P.pair Q.pair
  id P :=
    @CrystallineConnectionPair.Hom.id A _ p _ _ I γ C _ _ ι π hπ J hJ hIC hpnil hIJ E hE
      γbar P.M P.addCommGroup P.module P.pair
  comp {P Q R} f g :=
    @CrystallineConnectionPair.Hom.comp A _ p _ _ I γ C _ _ ι π hπ J hJ hIC hpnil hIJ E hE
      γbar P.M Q.M R.M P.addCommGroup Q.addCommGroup R.addCommGroup P.module Q.module
      R.module P.pair Q.pair R.pair f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end CrystallineConnectionPair

end
