module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.Torsor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.Trivial

/-!
# Restriction of infinitesimal extensions along a trivialization

Pushforward along a chosen left inverse of a first-order thickening converts an infinitesimal
sequence into an `𝒪_X`-module extension of `ℱ` by `𝒦`, hence an `Ext¹` class.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian (Ext)
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
open AlgebraicGeometry.RingedSpace.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules
namespace InfinitesimalExtension

variable {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]

/-- Identification `π_* i_* M ≅ M` induced by `i ≫ π = 𝟙 X`. -/
def retractPushforwardIso (τ : Trivialization i) (M : X.Modules) :
    (τ.retraction _*).obj ((i _*).obj M) ≅ M :=
  (pushforwardCompIso i τ.retraction).symm.app M ≪≫
    eqToIso (congrArg (fun f : X ⟶ X ↦ (f _*).obj M) τ.id) ≪≫
      (SheafOfModules.pushforwardId X.ringCatSheaf).app M

/-- The endpoint maps obtained by restriction along a retraction compose to zero. -/
theorem restrictionShortComplex_zero (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    (E : InfinitesimalExtension i F K c) :
    ((retractPushforwardIso τ K).inv ≫ (τ.retraction _*).map E.ι) ≫
      ((τ.retraction _*).map E.π ≫ (retractPushforwardIso τ F).hom) = 0 := sorry

/-- Restriction of scalars along `π^♯` gives an `𝒪_X`-module short complex. -/
def restrictionShortComplex (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    (E : InfinitesimalExtension i F K c) : ShortComplex X.Modules :=
  ShortComplex.mk
    ((retractPushforwardIso τ K).inv ≫ (τ.retraction _*).map E.ι)
    ((τ.retraction _*).map E.π ≫ (retractPushforwardIso τ F).hom)
    (restrictionShortComplex_zero τ E)

/-- Restriction along a retraction preserves the short exact sequence of an infinitesimal extension. -/
theorem restrictionShortComplex_shortExact (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    (E : InfinitesimalExtension i F K c) :
    (restrictionShortComplex τ E).ShortExact := sorry

/-- The middle term of the restricted sequence is `π_* ℱ'`. -/
theorem restrictionShortComplex_module (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    (E : InfinitesimalExtension i F K c) :
    (restrictionShortComplex τ E).X₂ = (τ.retraction _*).obj E.module := rfl

/-- The restricted inclusion is the pushforward of `ι` after identifying `π_* i_* 𝒦` with `𝒦`. -/
theorem restrictionShortComplex_f (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    (E : InfinitesimalExtension i F K c) :
    (restrictionShortComplex τ E).f =
      (retractPushforwardIso τ K).inv ≫ (τ.retraction _*).map E.ι := rfl

/-- The restricted projection is the pushforward of `π` after identifying `π_* i_* ℱ` with `ℱ`. -/
theorem restrictionShortComplex_g (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    (E : InfinitesimalExtension i F K c) :
    (restrictionShortComplex τ E).g =
      (τ.retraction _*).map E.π ≫ (retractPushforwardIso τ F).hom := rfl

/-- The pushed-forward middle map commutes with the restricted inclusion. -/
theorem restrictionShortComplex_map_comm_f (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    {E₁ E₂ : InfinitesimalExtension i F K c} (φ : Hom E₁ E₂) :
    (restrictionShortComplex τ E₁).f ≫ (τ.retraction _*).map φ.hom =
      (restrictionShortComplex τ E₂).f := sorry

/-- The pushed-forward middle map commutes with the restricted projection. -/
theorem restrictionShortComplex_map_comm_g (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    {E₁ E₂ : InfinitesimalExtension i F K c} (φ : Hom E₁ E₂) :
    (τ.retraction _*).map φ.hom ≫ (restrictionShortComplex τ E₂).g =
      (restrictionShortComplex τ E₁).g := sorry

/-- A morphism of infinitesimal extensions induces a short-complex morphism with identity endpoints. -/
def restrictionShortComplex_map (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    {E₁ E₂ : InfinitesimalExtension i F K c} (φ : Hom E₁ E₂) :
    restrictionShortComplex τ E₁ ⟶ restrictionShortComplex τ E₂ where
  τ₁ := 𝟙 K
  τ₂ := (τ.retraction _*).map φ.hom
  τ₃ := 𝟙 F
  comm₁₂ := (Category.id_comp _).trans (restrictionShortComplex_map_comm_f τ φ).symm
  comm₂₃ := (restrictionShortComplex_map_comm_g τ φ).trans (Category.comp_id _).symm

/-- The middle component of the restricted short-complex morphism is the pushed-forward map. -/
theorem restrictionShortComplex_map_τ₂ (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    {E₁ E₂ : InfinitesimalExtension i F K c} (φ : Hom E₁ E₂) :
    (restrictionShortComplex_map τ φ).τ₂ = (τ.retraction _*).map φ.hom := rfl

/-- The canonical degree-one class of an infinitesimal extension restricted along a retraction. -/
def extClass [HasExt.{u} X.Modules] (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    (E : InfinitesimalExtension i F K c) : Ext F K 1 :=
  (restrictionShortComplex_shortExact τ E).extClass

/-- Endpoint-preserving morphisms preserve the canonical class of the restricted extension. -/
theorem extClass_hom [HasExt.{u} X.Modules] (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    {E₁ E₂ : InfinitesimalExtension i F K c} (φ : Hom E₁ E₂) :
    extClass τ E₁ = extClass τ E₂ := sorry

/-- Restriction along a retraction assigns a canonical degree-one class to an isomorphism class. -/
def extClassOnIsoClass [HasExt.{u} X.Modules] (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    IsoClass i F K c → Ext F K 1 :=
  Quotient.lift (fun E ↦ extClass τ E) fun E₁ E₂ h ↦ by
    obtain ⟨φ⟩ := (h : Nonempty (Hom E₁ E₂))
    exact extClass_hom τ φ

/-- The descended restriction-class map computes on any representative. -/
theorem extClassOnIsoClass_mk [HasExt.{u} X.Modules] (τ : Trivialization i)
    {F K : X.Modules} {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    (E : InfinitesimalExtension i F K c) :
    extClassOnIsoClass τ c (IsoClass.mk E) = extClass τ E := rfl

/-- Restriction along a retraction classifies infinitesimal extensions with a fixed ideal action. -/
theorem extClass_bijective [HasExt.{u} X.Modules] (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    Function.Bijective (extClassOnIsoClass τ c) := sorry

/-- The explicit split infinitesimal extension represents zero after restriction along its retraction. -/
theorem extClass_trivial [HasExt.{u} X.Modules] (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    extClass τ (trivialExtension τ c) = 0 := sorry

end InfinitesimalExtension
end AlgebraicGeometry.RingedSpace.Modules
