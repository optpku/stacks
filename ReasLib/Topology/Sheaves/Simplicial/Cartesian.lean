module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.Topology.Sheaves.Simplicial.Augmentation.Coefficients

/-!
# Cartesian sheaves on simplicial spaces

A sheaf is cartesian when its adjunction-mate comparison along every simplex operator
is an isomorphism. Augmentation inverse image takes values in the full subcategory
of cartesian sheaves.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open Functor
open scoped Simplicial MorphismOfTopoiIn

noncomputable section

namespace CategoryTheory.SimplicialObject

variable (Y : SimplicialObject TopCat.{u})

/-- The natural transformation `u_φ ⋙ ι_n ⟶ ι_m` whose component at `V` is the
simplex operator `φ`. -/
def componentNatTrans {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    Opens.map (Y.map φ.op) ⋙ component Y n ⟶ component Y m where
  app U := DiagramOpens.homMk φ.op fun x hx ↦ hx
  naturality := sorry

/-- The composite of pullback along `Y.map φ.op` with inclusion at degree `n` is continuous. -/
instance component_comp_opensMap_isContinuous {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    (Opens.map (Y.map φ.op) ⋙ component Y n).IsContinuous
      (Opens.grothendieckTopology (Y.obj (op ⦋m⦌))) (zariskiTopology Y) :=
  isContinuous_comp (Opens.map (Y.map φ.op)) (component Y n)
    (Opens.grothendieckTopology (Y.obj (op ⦋m⦌)))
    (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (zariskiTopology Y)

/-- Left Kan extensions of coefficient-`A` presheaves along opposite open-map functors
of simplex operators of `Y`. -/
class HasOpensMapLeftKanExtension (A : Type (u + 1)) [Category.{u} A] : Prop where
  /-- Each simplex operator of `Y` admits left Kan extension of `A`-valued presheaves. -/
  out : ∀ (m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) (P : (Opens (Y.obj (op ⦋m⦌)))ᵒᵖ ⥤ A),
    (Opens.map (Y.map φ.op)).op.HasLeftKanExtension P

/-- The uniform open-map Kan-extension condition supplies left Kan extensions
along each simplex operator. -/
instance instHasLeftKanExtension_opensMap_of_hasOpensMapLeftKanExtension
    (A : Type (u + 1)) [Category.{u} A] [HasOpensMapLeftKanExtension Y A]
    (m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) (P : (Opens (Y.obj (op ⦋m⦌)))ᵒᵖ ⥤ A) :
    (Opens.map (Y.map φ.op)).op.HasLeftKanExtension P :=
  HasOpensMapLeftKanExtension.out m n φ P

/-- Open-map left Kan extensions exist for sheaves of sets. -/
instance hasOpensMapLeftKanExtension_type : HasOpensMapLeftKanExtension Y (Type u) where
  out _ _ _ _ := inferInstance

/-- Open-map left Kan extensions exist for abelian sheaves. -/
instance hasOpensMapLeftKanExtension_ab : HasOpensMapLeftKanExtension Y AddCommGrpCat.{u} where
  out _ _ _ _ := inferInstance

section CartesianSheaves

variable (A : Type (u + 1)) [Category.{u} A]
variable [∀ n : ℕ, HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) A]
variable [HasWeakSheafify (zariskiTopology Y) A]
variable [HasOpensMapLeftKanExtension Y A]

/-- Inverse image `f_φ⁻¹` of sheaves with coefficients in `A` along a simplex operator. -/
def sheafInverseImage {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    Sheaf (Opens.grothendieckTopology (Y.obj (op ⦋m⦌))) A ⥤
      Sheaf (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) A :=
  (Opens.map (Y.map φ.op)).sheafPullback A
    (Opens.grothendieckTopology (Y.obj (op ⦋m⦌)))
    (Opens.grothendieckTopology (Y.obj (op ⦋n⦌)))

/-- `sheafInverseImage` is sheaf pullback along `Opens.map (Y.map φ.op)`. -/
theorem sheafInverseImage_eq {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    sheafInverseImage Y A φ =
      (Opens.map (Y.map φ.op)).sheafPullback A
        (Opens.grothendieckTopology (Y.obj (op ⦋m⦌)))
        (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) :=
  rfl

/-- Direct-image form of `F(φ)`: restriction along `componentNatTrans` yields
`F_m ⟶ (f_φ)_* F_n`. -/
def transitionDirect {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌)
    (G : Sheaf (zariskiTopology Y) A) :
    (sheafComponent Y m A).obj G ⟶
      ((Opens.map (Y.map φ.op)).sheafPushforwardContinuous A
        (Opens.grothendieckTopology (Y.obj (op ⦋m⦌)))
        (Opens.grothendieckTopology (Y.obj (op ⦋n⦌)))).obj
        ((sheafComponent Y n A).obj G) :=
  (sheafPushforwardContinuousNatTrans (componentNatTrans Y φ) A
      (Opens.grothendieckTopology (Y.obj (op ⦋m⦌))) (zariskiTopology Y)).app G ≫
    (sheafPushforwardContinuousComp (Opens.map (Y.map φ.op)) (component Y n) A
        (Opens.grothendieckTopology (Y.obj (op ⦋m⦌)))
        (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (zariskiTopology Y)).inv.app G

/-- The comparison `F(φ) : f_φ⁻¹ F_m ⟶ F_n`, the mate of `transitionDirect`. -/
def sheafTransition {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌)
    (G : Sheaf (zariskiTopology Y) A) :
    (sheafInverseImage Y A φ).obj ((sheafComponent Y m A).obj G) ⟶
      (sheafComponent Y n A).obj G :=
  (((Opens.map (Y.map φ.op)).sheafAdjunctionContinuous A
      (Opens.grothendieckTopology (Y.obj (op ⦋m⦌)))
      (Opens.grothendieckTopology (Y.obj (op ⦋n⦌)))).homEquiv
    ((sheafComponent Y m A).obj G) ((sheafComponent Y n A).obj G)).symm
    (transitionDirect Y A φ G)

/-- The adjunction mate of `sheafTransition` is `transitionDirect`. -/
theorem sheafTransition_homEquiv {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌)
    (G : Sheaf (zariskiTopology Y) A) :
    (((Opens.map (Y.map φ.op)).sheafAdjunctionContinuous A
        (Opens.grothendieckTopology (Y.obj (op ⦋m⦌)))
        (Opens.grothendieckTopology (Y.obj (op ⦋n⦌)))).homEquiv
      ((sheafComponent Y m A).obj G) ((sheafComponent Y n A).obj G))
      (sheafTransition Y A φ G) =
    transitionDirect Y A φ G :=
  ((Opens.map (Y.map φ.op)).sheafAdjunctionContinuous A
    (Opens.grothendieckTopology (Y.obj (op ⦋m⦌)))
    (Opens.grothendieckTopology (Y.obj (op ⦋n⦌)))).homEquiv _ _ |>.apply_symm_apply
      (transitionDirect Y A φ G)

/-- A sheaf on `Y_Zar` is cartesian when `F(φ) : f_φ⁻¹ F_m ⟶ F_n` is an isomorphism for
every simplex operator `φ`. -/
class IsCartesian (G : Sheaf (zariskiTopology Y) A) : Prop where
  /-- Every simplex-operator comparison `F(φ)` is an isomorphism. -/
  isIso_transition : ∀ {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌), IsIso (sheafTransition Y A φ G)

/-- Cartesianness is equivalent to every `F(φ)` being an isomorphism. -/
theorem isCartesian_iff (G : Sheaf (zariskiTopology Y) A) :
    IsCartesian Y A G ↔
      ∀ {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌), IsIso (sheafTransition Y A φ G) :=
  ⟨fun h ↦ h.isIso_transition, fun h ↦ ⟨h⟩⟩

/-- A sheaf whose every simplex-operator comparison is an isomorphism is cartesian. -/
instance instIsCartesian_of_isIso (G : Sheaf (zariskiTopology Y) A)
    [h : ∀ {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌), IsIso (sheafTransition Y A φ G)] :
    IsCartesian Y A G where
  isIso_transition := h

/-- Every simplex-operator comparison of a cartesian sheaf is an isomorphism. -/
instance instIsIso_sheafTransition (G : Sheaf (zariskiTopology Y) A)
    [IsCartesian Y A G] {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    IsIso (sheafTransition Y A φ G) :=
  IsCartesian.isIso_transition φ

/-- The isomorphism `F(φ) : f_φ⁻¹ F_m ≅ F_n` attached to a cartesian sheaf. -/
def transitionIso (G : Sheaf (zariskiTopology Y) A) [IsCartesian Y A G]
    {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    (sheafInverseImage Y A φ).obj ((sheafComponent Y m A).obj G) ≅
      (sheafComponent Y n A).obj G :=
  asIso (sheafTransition Y A φ G)

/-- The forward map of `transitionIso` is `sheafTransition`. -/
theorem transitionIso_hom (G : Sheaf (zariskiTopology Y) A) [IsCartesian Y A G]
    {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    (transitionIso Y A G φ).hom = sheafTransition Y A φ G :=
  rfl

/-- The object property of being a cartesian sheaf on `Y_Zar`. -/
abbrev cartesianProperty : ObjectProperty (Sheaf (zariskiTopology Y) A) :=
  fun G ↦ IsCartesian Y A G

/-- The category of cartesian sheaves on `Y_Zar`. -/
abbrev Cartesian := (cartesianProperty Y A).FullSubcategory

/-- The underlying sheaf of an object of `Cartesian` is cartesian. -/
theorem cartesian_isCartesian (G : Cartesian Y A) : IsCartesian Y A G.obj :=
  G.property

end CartesianSheaves

variable {Y}

/-- Inverse image `a⁻¹ F` of a sheaf on `X` is cartesian on `Y_Zar`. -/
instance inverseImage_isCartesian {X : TopCat.{u}} (a : Y ⟶ constSpace X)
    (B : Type (u + 1)) [Category.{u} B]
    [HasWeakSheafify (zariskiTopology Y) B]
    [HasWeakSheafify (zariskiTopology (constSpace X)) B]
    [HasWeakSheafify (Opens.grothendieckTopology X) B]
    [∀ n : ℕ, HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) B]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ B, (zariskiMap a).op.HasLeftKanExtension P]
    [HasOpensMapLeftKanExtension Y B]
    (F : Sheaf (Opens.grothendieckTopology X) B) :
    IsCartesian Y B ((inverseImage a B).obj F) :=
  sorry

/-- Inverse image of a set-valued sheaf along the geometric augmentation is cartesian. -/
public instance augmentationMorphism_inverseImage_isCartesian {X : TopCat.{u}}
    (a : Y ⟶ constSpace X)
    [HasSheafify (zariskiTopology (constSpace X)) (Type u)]
    [HasSheafify (zariskiTopology Y) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
    [∀ n : ℕ, HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u, (zariskiMap a).op.HasLeftKanExtension P]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u,
      (constProjection X).op.HasPointwiseRightKanExtension P]
    (F : Sheaf (Opens.grothendieckTopology X) (Type u)) :
    IsCartesian Y (Type u) ((augmentationMorphism a)⁻¹.obj F) :=
  sorry

end CategoryTheory.SimplicialObject

end
