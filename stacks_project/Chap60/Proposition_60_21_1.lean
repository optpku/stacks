/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import stacks_project.Chap60.Lemma_60_18_2
public import stacks_project.Chap60.«60_8_1_2»
public import stacks_project.Chap60.Proposition_60_21_1_Sections
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline
open AlgebraicGeometry.Scheme.Modules
open CompletedCris
open CrystallineModuleSheaf

universe u w

variable {p : ℕ} [Fact (Nat.Prime p)]
variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γS : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γS V).IsDPMorphism (γS (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- Source hypothesis (2): comparisons `c_φ` are epimorphisms whenever the thickening
map is a closed immersion. -/
def comparison_epi_of_closedImmersion
    (F : CrisModuleSheaf S I γS h_compatible X x₀) : Prop :=
  ∀ {T T' : smallCrystallineSite S I γS h_compatible X x₀} (φ : T ⟶ T'),
    IsClosedImmersion φ.hom.thickening → Epi (F.comparison φ)

/-- Hypothesis (2) applies to a closed immersion of thickenings. -/
theorem comparison_epi_of_closedImmersion_apply
    {F : CrisModuleSheaf S I γS h_compatible X x₀}
    (h : comparison_epi_of_closedImmersion S I γS h_compatible X x₀ F)
    {T T' : smallCrystallineSite S I γS h_compatible X x₀} (φ : T ⟶ T')
    (hφ : IsClosedImmersion φ.hom.thickening) :
    Epi (F.comparison φ) :=
  sorry


variable {A : Type u} [CommRing A] {IA : Ideal A} (γA : DividedPowers IA)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type u} [CommRing C] [Algebra A C]
variable (hIC : Ideal.map (algebraMap A C) IA = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
variable (hπ : Function.Surjective π)
variable (J : (n : ℕ) → Ideal (tensorPowerCarrier A ι n))
variable (hJ : ∀ n, J n = RingHom.ker (tensorPowerAlgHom π n).toRingHom)
variable (hIJ : ∀ n, Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) IA ≤ J n)
variable (E : (n : ℕ) →
    DividedPowerEnvelope IA γA (algebraMap A (tensorPowerCarrier A ι n)) (J n) (hIJ n))
variable (hE : ∀ n, DividedPowerEnvelope.IsUniversal γA
    (algebraMap A (tensorPowerCarrier A ι n)) (hIJ n) (E n))
variable (N : ℕ → ℕ)
variable (hN : ∀ n, Ideal.span {(p : (E n).D)} ^ N n ≤ (E n).D.ideal)
variable (γhat : (n : ℕ) → DividedPowers (RingHom.ker
    (AdicCompletion.toQuotient (Ideal.span {(p : (E n).D)}) (E n).D.ideal (N n) (hN n))))
variable (hγhat : ∀ n, DividedPowers.IsDPMorphism (E n).D.dividedPowers (γhat n)
    (algebraMap (E n).D (AdicCompletion (Ideal.span {(p : (E n).D)}) (E n).D)))
variable [HasLimits AddCommGrpCat.{u}]
variable [HasBinaryProducts
  (CompletedCrisObject p A IA γA C (algebraMap A C) hIC hpnil)ᵒᵖ]
variable (eX : Spec (.of C) ⟶ X)

omit S I γS h_compatible s X x₀ h_p π hπ J hJ hIJ E hE N hN γhat hγhat ι in
/-- The source object over `X` associated to an affine divided-power thickening of `C`. -/
noncomputable def affineCrisOppOver
    {X : Scheme.{u}} (eX : Spec (.of C) ⟶ X)
    (T : DividedPowerThickening.Cris γA (algebraMap A C) hIC hpnil) : Over X :=
  Over.mk (Spec.map (CommRingCat.ofHom T.obj.quotient) ≫ eX)

omit π hπ J hJ hIJ E hE N hN γhat hγhat ι in
/-- Underlying divided-power ring of a `Cris` thickening object. -/
def crisThickeningRing
    (T : DividedPowerThickening.Cris γA (algebraMap A C) hIC hpnil) :
    DividedPowerRing :=
  T.obj.B

/-- Divided powers on the thickening ring of a `Cris` object. -/
def crisThickeningDividedPowers
    (T : DividedPowerThickening.Cris γA (algebraMap A C) hIC hpnil) :
    DividedPowers (crisThickeningRing γA hIC hpnil T).ideal :=
  (crisThickeningRing γA hIC hpnil T).dividedPowers

/-- The thickening ring is the `B` component of the underlying object. -/
theorem crisThickeningRing_spec
    (T : DividedPowerThickening.Cris γA (algebraMap A C) hIC hpnil) :
    crisThickeningRing γA hIC hpnil T = T.obj.B :=
  sorry

/-- The divided powers of a `Cris` thickening are those of its thickening ring. -/
theorem crisThickeningDividedPowers_spec
    (T : DividedPowerThickening.Cris γA (algebraMap A C) hIC hpnil) :
    crisThickeningDividedPowers γA hIC hpnil T =
      (crisThickeningRing γA hIC hpnil T).dividedPowers :=
  sorry

/-- Underlying divided-power morphism of a morphism of thickenings. -/
def dividedPowerThickeningHomMap
    {T T' : DividedPowerThickening.Cris γA (algebraMap A C) hIC hpnil}
    (φ : T ⟶ T') :
    DividedPowers.DPMorphism
      (crisThickeningDividedPowers γA hIC hpnil T)
      (crisThickeningDividedPowers γA hIC hpnil T') :=
  φ.hom.map

/-- The thickening morphism projects to its underlying divided-power map. -/
theorem dividedPowerThickeningHomMap_apply
    {T T' : DividedPowerThickening.Cris γA (algebraMap A C) hIC hpnil}
    (φ : T ⟶ T') :
    dividedPowerThickeningHomMap γA hIC hpnil φ = φ.hom.map :=
  sorry

omit π hπ J hJ hIJ E hE N hN γhat hγhat ι in
/-- Inclusion of affine `Cris(C/A)ᵒᵖ` into the small crystalline site of `(X/S)`. -/
noncomputable def affineCrisOppInclusion
    [IsAffine X] [IsAffine S]
    (eX : Spec (.of C) ⟶ X) :
    (DividedPowerThickening.Cris γA (algebraMap A C) hIC hpnil)ᵒᵖ ⥤
      smallCrystallineSite S I γS h_compatible X x₀ :=
  { obj := fun T ↦
      { obj := (crystallineTrivialFunctor p S I γS h_compatible s X x₀ h_p).obj
          (affineCrisOppOver γA hIC hpnil eX T.unop)
        property := sorry }
    map := fun {T T'} f ↦
      ObjectProperty.homMk
        ((crystallineTrivialFunctor p S I γS h_compatible s X x₀ h_p).map
          (Over.homMk
            (Spec.map (CommRingCat.ofHom
              (DividedPowerRing.quotientMap
                (dividedPowerThickeningHomMap γA hIC hpnil f.unop))))
            sorry))
    map_id := sorry
    map_comp := sorry }

omit π hπ J hJ hIJ E hE N hN γhat hγhat ι in
/-- The affine inclusion sends a thickening to the identity crystalline object on its
closed fibre over `X`. -/
theorem affineCrisOppInclusion_obj
    [IsAffine X] [IsAffine S]
    (T : (DividedPowerThickening.Cris γA (algebraMap A C) hIC hpnil)ᵒᵖ) :
    (affineCrisOppInclusion S I γS h_compatible s X x₀ h_p γA hIC hpnil eX).obj T =
      { obj := (crystallineTrivialFunctor p S I γS h_compatible s X x₀ h_p).obj
          (affineCrisOppOver γA hIC hpnil eX T.unop)
        property := sorry } :=
  sorry

omit π hπ J hJ hIJ E hE N hN γhat hγhat ι in
/-- Restriction of an abelian sheaf on `Cris(X/S)` to the affine chaotic site `Cris(C/A)ᵒᵖ`. -/
noncomputable def restrictToAffineCrisOpp
    [IsAffine X] [IsAffine S]
    (eX : Spec (.of C) ⟶ X)
    (F : Sheaf (smallCrystallineTopology p S I γS h_compatible s X x₀ h_p)
      AddCommGrpCat.{u}) :
    Sheaf (⊥ : GrothendieckTopology (crisOppSite γA (algebraMap A C) hIC hpnil))
      AddCommGrpCat.{u} where
  obj := (affineCrisOppInclusion S I γS h_compatible s X x₀ h_p γA hIC hpnil eX).op ⋙ F.obj
  property := Presheaf.isSheaf_bot _

omit π hπ J hJ hIJ E hE N hN γhat hγhat ι in
/-- Restriction to the affine chaotic site is precomposition with the opposite inclusion. -/
theorem restrictToAffineCrisOpp_obj
    [IsAffine X] [IsAffine S]
    (F : Sheaf (smallCrystallineTopology p S I γS h_compatible s X x₀ h_p)
      AddCommGrpCat.{u}) :
    (restrictToAffineCrisOpp S I γS h_compatible s X x₀ h_p γA hIC hpnil eX F).obj =
      (affineCrisOppInclusion S I γS h_compatible s X x₀ h_p γA hIC hpnil eX).op ⋙ F.obj :=
  sorry

/-- The ideal sheaf on `Spec A` is the one associated with `IA`. -/
def specIdealEqOfIdealTop (IA : Ideal A) (I : (Spec.{u} (.of A)).IdealSheafData) : Prop :=
  I = Scheme.IdealSheafData.ofIdealTop
    (Ideal.comap (Scheme.ΓSpecIso (.of A)).hom.hom IA)

/-- Global divided powers on `Spec A` recover `γA` along `ΓSpecIso`. -/
def specDividedPowersEq (IA : Ideal A) (γA : DividedPowers IA)
    (I : (Spec.{u} (.of A)).IdealSheafData)
    (γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V)) : Prop :=
  DividedPowers.IsDPMorphism γA
    (γS ⟨⊤, isAffineOpen_top (Spec (.of A))⟩)
    (Scheme.ΓSpecIso (.of A)).inv.hom

/-- The closed immersion `Spec C ⟶ V(I)` is induced by `algebraMap A C`,
equivalently by the quotient map `A / IA → C` along `hIC`. -/
def IsCanonicalCrisStructureMap
    (I : (Spec.{u} (.of A)).IdealSheafData)
    (x₀ : Spec.{u} (.of C) ⟶ I.subscheme) : Prop :=
  x₀ ≫ I.subschemeι = Spec.map (CommRingCat.ofHom (algebraMap A C))

/-- The structure map of `Spec C` over `V(I)` recovers `Spec.map` of `algebraMap A C`. -/
theorem IsCanonicalCrisStructureMap.apply
    {I : (Spec.{u} (.of A)).IdealSheafData}
    {x₀ : Spec.{u} (.of C) ⟶ I.subscheme}
    (h : IsCanonicalCrisStructureMap I x₀) :
    x₀ ≫ I.subschemeι = Spec.map (CommRingCat.ofHom (algebraMap A C)) :=
  sorry

omit S I γS h_compatible s X x₀ h_p eX in
/-- Proposition 60.21.1: with `S = Spec A` and `X = Spec C` as in §60.21, if `F` is
locally quasi-coherent and comparisons `c_f` are surjective for closed immersions of
thickenings, then the complex `M(0) → M(1) → M(2) → ⋯` with
`M(n) = lim_e Γ((X, T(n)_e, δ(n)), F)` computes `RΓ(Cris(X/S), F)`. -/
@[stacks 07JN]
theorem affineCrisSectionsComplex_computes_derivedGlobalSections
    (I : (Spec.{u} (.of A)).IdealSheafData)
    (γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : (Spec.{u} (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
        (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
          ((Spec (.of A)).presheaf.map
            (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom)
    (s : Spec.{u} (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (x₀ : Spec.{u} (.of C) ⟶ I.subscheme)
    (h_p : ∀ U : (Spec.{u} (.of C)).affineOpens,
      IsNilpotent (p : Γ(Spec (.of C), U)))
    (hI : specIdealEqOfIdealTop IA I)
    (hγ : specDividedPowersEq IA γA I γS)
    (hx₀ : IsCanonicalCrisStructureMap I x₀)
    [HasSheafify
      (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
        (Spec (.of C)) x₀ h_p)
      AddCommGrpCat.{u}]
    [HasSheafify (chaoticTopology (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
      AddCommGrpCat.{u}]
    [HasTerminal (smallCrystallineSite (Spec (.of A)) I γS h_compatible
      (Spec (.of C)) x₀)]
    [HasTerminal (chaoticSite (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
        (Spec (.of C)) x₀ h_p) AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (chaoticTopology (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
        AddCommGrpCat.{u})]
    [HasSheafify (⊥ : GrothendieckTopology
      (crisOppSite γA (algebraMap A C) hIC hpnil)) AddCommGrpCat.{u}]
    [HasExt (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
      (Spec (.of C)) x₀ h_p) AddCommGrpCat.{u})]
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
    [ModuleSheaf.IsLocallyQuasiCoherent F]
    (h_epi : comparison_epi_of_closedImmersion (Spec (.of A)) I γS h_compatible
      (Spec (.of C)) x₀ F) :
    IsIsomorphic
      ((siteAbelianSectionsDerived
          (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
            (Spec (.of C)) x₀ h_p)
          (⊤_ (smallCrystallineSite (Spec (.of A)) I γS h_compatible
            (Spec (.of C)) x₀))).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
              (Spec (.of C)) x₀ h_p) AddCommGrpCat.{u}) 0).obj
          (toAbelianSheaf p (Spec (.of A)) I γS h_compatible s (Spec (.of C)) x₀ h_p
            F)))
      ((DerivedCategory.Q).obj
        ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}).obj
          (affineCrisSectionsComplex γA hIC hpnil π hπ J hJ hIJ E hE N hN γhat hγhat
            (restrictToAffineCrisOpp (Spec (.of A)) I γS h_compatible s
              (Spec (.of C)) x₀ h_p γA hIC hpnil (𝟙 _)
              (toAbelianSheaf p (Spec (.of A)) I γS h_compatible s
                (Spec (.of C)) x₀ h_p F))))) :=
  sorry

omit S I γS h_compatible s X x₀ h_p eX in
/-- Degreewise cohomology of `RΓ(Cris(X/S), F)` agrees with homology of `M(*)`. -/
theorem affineCrisSectionsComplex_computes_cohomology
    (I : (Spec.{u} (.of A)).IdealSheafData)
    (γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : (Spec.{u} (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
        (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
          ((Spec (.of A)).presheaf.map
            (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom)
    (s : Spec.{u} (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (x₀ : Spec.{u} (.of C) ⟶ I.subscheme)
    (h_p : ∀ U : (Spec.{u} (.of C)).affineOpens,
      IsNilpotent (p : Γ(Spec (.of C), U)))
    (hI : specIdealEqOfIdealTop IA I)
    (hγ : specDividedPowersEq IA γA I γS)
    (hx₀ : IsCanonicalCrisStructureMap I x₀)
    [HasSheafify
      (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
        (Spec (.of C)) x₀ h_p)
      AddCommGrpCat.{u}]
    [HasSheafify (chaoticTopology (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
      AddCommGrpCat.{u}]
    [HasTerminal (smallCrystallineSite (Spec (.of A)) I γS h_compatible
      (Spec (.of C)) x₀)]
    [HasTerminal (chaoticSite (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
        (Spec (.of C)) x₀ h_p) AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (chaoticTopology (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
        AddCommGrpCat.{u})]
    [HasSheafify (⊥ : GrothendieckTopology
      (crisOppSite γA (algebraMap A C) hIC hpnil)) AddCommGrpCat.{u}]
    [HasExt (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
      (Spec (.of C)) x₀ h_p) AddCommGrpCat.{u})]
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
    [ModuleSheaf.IsLocallyQuasiCoherent F]
    (h_epi : comparison_epi_of_closedImmersion (Spec (.of A)) I γS h_compatible
      (Spec (.of C)) x₀ F)
    (n : ℕ) :
    IsIsomorphic
      ((Sheaf.functorH
          (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
            (Spec (.of C)) x₀ h_p) n).obj
        (toAbelianSheaf p (Spec (.of A)) I γS h_compatible s (Spec (.of C)) x₀ h_p F))
      ((affineCrisSectionsComplex γA hIC hpnil π hπ J hJ hIJ E hE N hN γhat hγhat
          (restrictToAffineCrisOpp (Spec (.of A)) I γS h_compatible s
            (Spec (.of C)) x₀ h_p γA hIC hpnil (𝟙 _)
            (toAbelianSheaf p (Spec (.of A)) I γS h_compatible s
              (Spec (.of C)) x₀ h_p F))).homology n) :=
  sorry
