/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import ReasLib.CategoryTheory.Abelian.Extension.Ext
public import stacks_project.Chap91.Lemma_91_4_3
public import stacks_project.Chap91.Remark_91_4_6_Trivial

/-!
# Restriction of 08L4 extensions along a trivialization

Pushforward along a chosen left inverse of a first-order thickening converts an 08L4
sequence into an `𝒪_X`-module extension of `ℱ` by `𝒦`, hence an `Ext¹` class.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
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

/-- The canonical isomorphism `(𝟙 X)_* M ≅ M`. -/
def idPushforwardIso (M : X.Modules) : ((𝟙 X) _*).obj M ≅ M where
  hom := idPushforwardHom M
  inv :=
    (pullbackPushforwardAdjunction (𝟙 X)).unit.app M ≫
      ((𝟙 X) _*).map ((pullbackIdIso X).hom.app M)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `idPushforwardIso` is `idPushforwardHom`. -/
theorem idPushforwardIso_hom (M : X.Modules) :
    (idPushforwardIso M).hom = idPushforwardHom M := sorry

/-- Identification `π_* i_* M ≅ M` induced by `i ≫ π = 𝟙 X`. -/
def retractPushforwardIso (τ : Trivialization i) (M : X.Modules) :
    (τ.retraction _*).obj ((i _*).obj M) ≅ M :=
  (pushforwardCompIso i τ.retraction).symm.app M ≪≫
    eqToIso (congrArg (fun f : X ⟶ X ↦ (f _*).obj M) τ.id) ≪≫
      idPushforwardIso M

/-- Restriction of scalars along `π^♯` converts an 08L4 sequence into an `𝒪_X`-extension. -/
def restrictExtension (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    (E : InfinitesimalExtension i F K c) : Extension K F where
  E := (τ.retraction _*).obj E.module
  f := (retractPushforwardIso τ K).inv ≫ (τ.retraction _*).map E.ι
  g := (τ.retraction _*).map E.π ≫ (retractPushforwardIso τ F).hom
  zero := sorry
  shortExact := sorry

/-- The middle term of the restricted sequence is `π_* ℱ'`. -/
theorem restrictExtension_module (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    (E : InfinitesimalExtension i F K c) :
    (restrictExtension τ E).E = (τ.retraction _*).obj E.module := sorry

/-- The restricted inclusion is the pushforward of `ι` after identifying `π_* i_* 𝒦` with `𝒦`. -/
theorem restrictExtension_f (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    (E : InfinitesimalExtension i F K c) :
    (restrictExtension τ E).f =
      (retractPushforwardIso τ K).inv ≫ (τ.retraction _*).map E.ι := sorry

/-- The restricted projection is the pushforward of `π` after identifying `π_* i_* ℱ` with `ℱ`. -/
theorem restrictExtension_g (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    (E : InfinitesimalExtension i F K c) :
    (restrictExtension τ E).g =
      (τ.retraction _*).map E.π ≫ (retractPushforwardIso τ F).hom := sorry

/-- A morphism of 08L4 extensions induces a morphism of the restricted `𝒪_X`-extensions. -/
def restrictExtension_map (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    {E₁ E₂ : InfinitesimalExtension i F K c} (φ : Hom E₁ E₂) :
    Extension.Hom (restrictExtension τ E₁) (restrictExtension τ E₂) where
  hom := (τ.retraction _*).map φ.hom
  comm_f := sorry
  comm_g := sorry

/-- The underlying middle map of `restrictExtension_map` is `π_*` of the 08L4 morphism. -/
theorem restrictExtension_map_hom (τ : Trivialization i) {F K : X.Modules}
    {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}
    {E₁ E₂ : InfinitesimalExtension i F K c} (φ : Hom E₁ E₂) :
    (restrictExtension_map τ φ).hom = (τ.retraction _*).map φ.hom := sorry

/-- The based chart of isomorphism classes against the trivial extension, as `𝒪_X`-extension
classes. -/
def extensionClassEquiv (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    IsoClass i F K c ≃ ExtensionClass K F :=
  (isoClassEquiv (trivialExtension τ c)).symm

/-- The based chart is torsor subtraction against the trivial extension. -/
theorem extensionClassEquiv_apply (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (p : IsoClass i F K c) :
    extensionClassEquiv τ c p = p -ᵥ IsoClass.mk (trivialExtension τ c) := sorry

/-- The trivial extension is the zero class in the `ExtensionClass` chart. -/
theorem extensionClassEquiv_zero (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    extensionClassEquiv τ c (IsoClass.mk (trivialExtension τ c)) = 0 := sorry

end InfinitesimalExtension
end AlgebraicGeometry.RingedSpace.Modules
