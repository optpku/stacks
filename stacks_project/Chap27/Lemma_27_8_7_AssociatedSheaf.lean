module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import ReasLib.Algebra.Group.Action.NatInt
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Module.Basic

/-!
# The sheaf associated to a graded module on `Proj`

This module constructs the associated sheaf from its local fraction description.  A section is a
family in the degree-zero homogeneous localizations at the points of an open which is locally
represented by one homogeneous fraction on a positive-degree standard open.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe uA uσ uτ

namespace AlgebraicGeometry.Proj

variable {A : Type uA} {σ : Type uσ} [CommRing A] [SetLike σ A]
variable [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {M : Type uA} [AddCommGroup M] [Module A M]
variable {τ : Type uτ} [SetLike τ M] [AddSubmonoidClass τ M]
variable (ℳ : ℤ → τ) [SetLike.GradedSMul 𝒜 ℳ]

/-- The carrier of the degree-zero part of a localized `ℤ`-graded module. -/
def degreeZeroLocalizedModuleSet (P : Submonoid A) : Set (LocalizedModule P M) :=
  { z | ∃ (n : ℕ) (m : ℳ (n : ℤ)) (s : 𝒜 n) (hs : (s : A) ∈ P),
      z = LocalizedModule.mk (m : M) ⟨(s : A), hs⟩ }

/-- Zero belongs to the degree-zero part of a localized graded module. -/
theorem zero_mem_degreeZeroLocalizedModuleSet (P : Submonoid A) :
    0 ∈ degreeZeroLocalizedModuleSet 𝒜 ℳ P := sorry

/-- The degree-zero part of a localized graded module is closed under addition. -/
theorem add_mem_degreeZeroLocalizedModuleSet (P : Submonoid A)
    {x y : LocalizedModule P M} (hx : x ∈ degreeZeroLocalizedModuleSet 𝒜 ℳ P)
    (hy : y ∈ degreeZeroLocalizedModuleSet 𝒜 ℳ P) :
    x + y ∈ degreeZeroLocalizedModuleSet 𝒜 ℳ P := sorry

/-- The degree-zero part is stable under the homogeneous-localization action. -/
theorem smul_mem_degreeZeroLocalizedModuleSet (P : Submonoid A)
    (r : HomogeneousLocalization 𝒜 P) {x : LocalizedModule P M}
    (hx : x ∈ degreeZeroLocalizedModuleSet 𝒜 ℳ P) :
    r • x ∈ degreeZeroLocalizedModuleSet 𝒜 ℳ P := sorry

/-- The degree-zero homogeneous localization of a `ℤ`-graded module at `P`. -/
noncomputable def degreeZeroLocalizedModule (P : Submonoid A) :
    Submodule (HomogeneousLocalization 𝒜 P) (LocalizedModule P M) where
  carrier := degreeZeroLocalizedModuleSet 𝒜 ℳ P
  zero_mem' := zero_mem_degreeZeroLocalizedModuleSet 𝒜 ℳ P
  add_mem' := add_mem_degreeZeroLocalizedModuleSet 𝒜 ℳ P
  smul_mem' := smul_mem_degreeZeroLocalizedModuleSet 𝒜 ℳ P

/-- Membership in `degreeZeroLocalizedModule` is the existence of a homogeneous fraction whose
numerator and denominator have the same nonnegative degree. -/
theorem mem_degreeZeroLocalizedModule_iff (P : Submonoid A)
    (z : LocalizedModule P M) :
    z ∈ degreeZeroLocalizedModule 𝒜 ℳ P ↔
      ∃ (n : ℕ) (m : ℳ (n : ℤ)) (s : 𝒜 n) (hs : (s : A) ∈ P),
        z = LocalizedModule.mk (m : M) ⟨(s : A), hs⟩ := sorry

/-- Enlarging denominators preserves the degree-zero localized module. -/
theorem liftOfLE_mem_degreeZeroLocalizedModule {P Q : Submonoid A} (hPQ : P ≤ Q)
    {z : LocalizedModule P M} (hz : z ∈ degreeZeroLocalizedModule 𝒜 ℳ P) :
    LocalizedModule.liftOfLE P Q hPQ z ∈ degreeZeroLocalizedModule 𝒜 ℳ Q := sorry

/-- The degree-zero localization away from a homogeneous element. -/
noncomputable abbrev awayModule {d : ℕ} (f : 𝒜 d) :=
  degreeZeroLocalizedModule 𝒜 ℳ (Submonoid.powers (f : A))

/-- The degree-zero localization at the homogeneous prime represented by `x`. -/
noncomputable abbrev atPointModule (x : AlgebraicGeometry.Proj 𝒜) :=
  degreeZeroLocalizedModule 𝒜 ℳ x.asHomogeneousIdeal.toIdeal.primeCompl

/-- Denominator enlargement from a standard open preserves degree-zero fractions. -/
noncomputable def awayToPoint {d : ℕ} (f : 𝒜 d)
    (x : AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) :
    awayModule 𝒜 ℳ f → atPointModule 𝒜 ℳ x.1 :=
  fun z ↦
    ⟨LocalizedModule.liftOfLE (Submonoid.powers (f : A))
        x.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr x.2) z,
      liftOfLE_mem_degreeZeroLocalizedModule 𝒜 ℳ (Submonoid.powers_le.mpr x.2) z.2⟩

/-- The point module carries the canonical action of the structure-sheaf stalk. -/
noncomputable instance atPointModule_stalkModule (x : AlgebraicGeometry.Proj 𝒜) :
    Module ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x) (atPointModule 𝒜 ℳ x) :=
  Module.compHom (atPointModule 𝒜 ℳ x)
    (AlgebraicGeometry.Proj.stalkIso 𝒜 x).hom.hom

/-- At a point of an open `U`, the point module is a module over the sections of the structure
sheaf on `U`, through the germ map. -/
noncomputable instance atPointModule_sectionModule
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) (x : U) :
    Module ((AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U)) (atPointModule 𝒜 ℳ x.1) :=
  Module.compHom (atPointModule 𝒜 ℳ x.1)
    ((AlgebraicGeometry.Proj 𝒜).presheaf.germ U x.1 x.2).hom

/-- Families of degree-zero localized elements over the points of an open. -/
abbrev PointFamily (U : (AlgebraicGeometry.Proj 𝒜).Opens) :=
  ∀ x : U, atPointModule 𝒜 ℳ x.1

/-- A point-family is locally representable if every point has a positive-degree standard-open
neighborhood on which the family comes from one degree-zero homogeneous fraction. -/
def IsLocallyRepresentable (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : PointFamily 𝒜 ℳ U) : Prop :=
  ∀ x : U,
    ∃ (d : ℕ) (f : 𝒜 d) (_ : 0 < d)
      (hU : AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) ≤ U)
      (z : awayModule 𝒜 ℳ f),
      x.1 ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) ∧
        ∀ y : AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A),
          s ⟨y.1, hU y.2⟩ = awayToPoint 𝒜 ℳ f y z

/-- The zero point-family is locally representable. -/
theorem isLocallyRepresentable_zero (U : (AlgebraicGeometry.Proj 𝒜).Opens) :
    IsLocallyRepresentable 𝒜 ℳ U 0 := sorry

/-- Locally representable point-families are closed under addition. -/
theorem IsLocallyRepresentable.add {U : (AlgebraicGeometry.Proj 𝒜).Opens}
    {s t : PointFamily 𝒜 ℳ U} (hs : IsLocallyRepresentable 𝒜 ℳ U s)
    (ht : IsLocallyRepresentable 𝒜 ℳ U t) :
    IsLocallyRepresentable 𝒜 ℳ U (s + t) := sorry

/-- Locally representable point-families are closed under multiplication by structure-sheaf
sections. -/
theorem IsLocallyRepresentable.smul {U : (AlgebraicGeometry.Proj 𝒜).Opens}
    (r : (AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U))
    {s : PointFamily 𝒜 ℳ U} (hs : IsLocallyRepresentable 𝒜 ℳ U s) :
    IsLocallyRepresentable 𝒜 ℳ U (r • s) := sorry

/-- The module of locally representable point-families on `U`. -/
noncomputable def associatedSectionsSubmodule
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) :
    Submodule ((AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U)) (PointFamily 𝒜 ℳ U) where
  carrier := IsLocallyRepresentable 𝒜 ℳ U
  zero_mem' := isLocallyRepresentable_zero 𝒜 ℳ U
  add_mem' := IsLocallyRepresentable.add 𝒜 ℳ
  smul_mem' := IsLocallyRepresentable.smul 𝒜 ℳ

/-- Sections of the associated graded-module sheaf on an open. -/
noncomputable abbrev AssociatedSections (U : (AlgebraicGeometry.Proj 𝒜).Opens) :=
  associatedSectionsSubmodule 𝒜 ℳ U

/-- Restricting a locally representable family to a smaller open preserves local
representability. -/
theorem restrictSection_isLocallyRepresentable
    {U V : (AlgebraicGeometry.Proj 𝒜).Opens} (hVU : V ≤ U)
    (s : AssociatedSections 𝒜 ℳ U) :
    IsLocallyRepresentable 𝒜 ℳ V (fun x ↦ s.1 ⟨x.1, hVU x.2⟩) := sorry

/-- Restriction of a locally representable section along an inclusion of opens. -/
noncomputable def restrictSection {U V : (AlgebraicGeometry.Proj 𝒜).Opens}
    (hVU : V ≤ U) (s : AssociatedSections 𝒜 ℳ U) : AssociatedSections 𝒜 ℳ V :=
  ⟨fun x ↦ s.1 ⟨x.1, hVU x.2⟩,
    restrictSection_isLocallyRepresentable 𝒜 ℳ hVU s⟩

/-- Restriction of associated sections preserves addition. -/
theorem restrictSection_add {U V : (AlgebraicGeometry.Proj 𝒜).Opens}
    (hVU : V ≤ U) (s t : AssociatedSections 𝒜 ℳ U) :
    restrictSection 𝒜 ℳ hVU (s + t) =
      restrictSection 𝒜 ℳ hVU s + restrictSection 𝒜 ℳ hVU t := sorry

/-- Restriction of associated sections is semilinear over restriction of structure-sheaf
sections. -/
theorem restrictSection_smul {U V : (AlgebraicGeometry.Proj 𝒜).Opens}
    (hVU : V ≤ U) (r : (AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U))
    (s : AssociatedSections 𝒜 ℳ U) :
    restrictSection 𝒜 ℳ hVU (r • s) =
      (AlgebraicGeometry.Proj 𝒜).presheaf.map (homOfLE hVU).op r •
        restrictSection 𝒜 ℳ hVU s := sorry

/-- The module object of associated sections on `U`. -/
noncomputable abbrev associatedSectionModule
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) :=
  ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U))
    (AssociatedSections 𝒜 ℳ U)

/-- The restriction map between the module objects of associated sections. -/
noncomputable def associatedRestrictionMap
    {U V : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ} (i : U ⟶ V) :
    associatedSectionModule 𝒜 ℳ U.unop ⟶
      (ModuleCat.restrictScalars ((AlgebraicGeometry.Proj 𝒜).presheaf.map i).hom).obj
        (associatedSectionModule 𝒜 ℳ V.unop) :=
  ModuleCat.ofHom
    (Y :=
      (ModuleCat.restrictScalars ((AlgebraicGeometry.Proj 𝒜).presheaf.map i).hom).obj
        (associatedSectionModule 𝒜 ℳ V.unop))
    { toFun := restrictSection 𝒜 ℳ i.unop.le
      map_add' := restrictSection_add 𝒜 ℳ i.unop.le
      map_smul' := restrictSection_smul 𝒜 ℳ i.unop.le }

/-- The associated restriction map on an identity morphism is the canonical identity map. -/
theorem associatedRestrictionMap_id (U : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ) :
    associatedRestrictionMap 𝒜 ℳ (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        ((AlgebraicGeometry.Proj 𝒜).presheaf.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom
          ((AlgebraicGeometry.Proj 𝒜).presheaf.map_id U))).inv.app _ := sorry

/-- Associated restriction maps compose functorially. -/
theorem associatedRestrictionMap_comp
    {U V W : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    associatedRestrictionMap 𝒜 ℳ (i ≫ j) =
      associatedRestrictionMap 𝒜 ℳ i ≫
        (ModuleCat.restrictScalars _).map (associatedRestrictionMap 𝒜 ℳ j) ≫
          (ModuleCat.restrictScalarsComp'
            ((AlgebraicGeometry.Proj 𝒜).presheaf.map i).hom
            ((AlgebraicGeometry.Proj 𝒜).presheaf.map j).hom
            ((AlgebraicGeometry.Proj 𝒜).presheaf.map (i ≫ j)).hom
            (congrArg CommRingCat.Hom.hom
              ((AlgebraicGeometry.Proj 𝒜).presheaf.map_comp i j))).inv.app _ := sorry

/-- The presheaf of modules whose sections are locally representable homogeneous fractions. -/
noncomputable def associatedPresheaf :
    PresheafOfModules (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj where
  obj U := associatedSectionModule 𝒜 ℳ U.unop
  map i := associatedRestrictionMap 𝒜 ℳ i
  map_id := associatedRestrictionMap_id 𝒜 ℳ
  map_comp := associatedRestrictionMap_comp 𝒜 ℳ

/-- Locally representable homogeneous-fraction sections satisfy the sheaf condition. -/
theorem associatedPresheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology (AlgebraicGeometry.Proj 𝒜))
      (associatedPresheaf 𝒜 ℳ).presheaf := sorry

/-- The deterministic `𝒪_{Proj(𝒜)}`-module sheaf associated to a `ℤ`-graded `A`-module. -/
noncomputable def associatedSheaf : (AlgebraicGeometry.Proj 𝒜).Modules where
  val := associatedPresheaf 𝒜 ℳ
  isSheaf := associatedPresheaf_isSheaf 𝒜 ℳ

/-- A degree-zero homogeneous fraction gives a section of the associated sheaf on its standard
open. -/
theorem awaySection_isLocallyRepresentable {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (z : awayModule 𝒜 ℳ f) :
    IsLocallyRepresentable 𝒜 ℳ (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))
      (fun x ↦ awayToPoint 𝒜 ℳ f x z) := sorry

/-- A degree-zero homogeneous fraction gives a section of the associated sheaf on its standard
open. -/
noncomputable def awaySection {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (z : awayModule 𝒜 ℳ f) :
    AssociatedSections 𝒜 ℳ (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) :=
  ⟨fun x ↦ awayToPoint 𝒜 ℳ f x z,
    awaySection_isLocallyRepresentable 𝒜 ℳ f hd z⟩

/-- The standard-open section map sends zero to zero. -/
theorem awaySection_zero {d : ℕ} (f : 𝒜 d) (hd : 0 < d) :
    awaySection 𝒜 ℳ f hd 0 = 0 := sorry

/-- The standard-open section map preserves addition. -/
theorem awaySection_add {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (x y : awayModule 𝒜 ℳ f) :
    awaySection 𝒜 ℳ f hd (x + y) =
      awaySection 𝒜 ℳ f hd x + awaySection 𝒜 ℳ f hd y := sorry

/-- The canonical standard-open section map is additive. -/
noncomputable def awaySectionAddHom {d : ℕ} (f : 𝒜 d) (hd : 0 < d) :
    awayModule 𝒜 ℳ f →+
      AssociatedSections 𝒜 ℳ (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) where
  toFun := awaySection 𝒜 ℳ f hd
  map_zero' := awaySection_zero 𝒜 ℳ f hd
  map_add' := awaySection_add 𝒜 ℳ f hd

/-- On a positive-degree standard open, the canonical fraction-to-section map is bijective. -/
theorem awaySectionAddHom_bijective {d : ℕ} (f : 𝒜 d) (hd : 0 < d) :
    Function.Bijective (awaySectionAddHom 𝒜 ℳ f hd) := sorry

/-- The sheaf associated to every graded module on `Proj` is quasi-coherent. -/
instance associatedSheaf_isQuasicoherent :
    (associatedSheaf 𝒜 ℳ).IsQuasicoherent := sorry

end AlgebraicGeometry.Proj
