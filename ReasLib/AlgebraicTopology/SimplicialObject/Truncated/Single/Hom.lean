/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Single.Functor
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Single.Compatibility

/-!
@stack 0190

# Hom descriptions for concentrated truncated simplicial objects

This leaf reconstructs morphisms to and from `Truncated.concentrated B k` from compatible
top-degree data and packages the resulting natural equivalences and extensionality principles.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open SimplexCategory
open scoped SimplexCategory.Truncated Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

namespace concentrated

variable [HasZeroObject A]

/-- The component supported in top degree associated to a map satisfying `FaceCondition`. -/
@[stacks 0190 "map from a concentrated object component"]
noncomputable def FaceMap.toHomApp {k : ℕ} {B : A}
    {V : SimplicialObject.Truncated A k}
    (g : FaceMap B V)
    (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    (concentrated B k).obj X ⟶ V.obj X :=
  if hX : X.unop.1.len = k then
    eqToHom (if_pos hX) ≫ g.1 ≫
      V.map
        (SimplexCategory.Truncated.Hom.tr
          (eqToHom (SimplexCategory.ext hX)) X.unop.property le_rfl).op
  else 0

/-- The component supported in top degree associated to a map satisfying
`DegeneracyCondition`. -/
@[stacks 0190 "map to a concentrated object component"]
noncomputable def DegeneracyMap.toHomApp {k : ℕ} {B : A}
    {V : SimplicialObject.Truncated A k}
    (g : DegeneracyMap V B)
    (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    V.obj X ⟶ (concentrated B k).obj X :=
  if hX : X.unop.1.len = k then
    V.map
        (SimplexCategory.Truncated.Hom.tr
          (eqToHom (SimplexCategory.ext hX).symm) le_rfl X.unop.property).op ≫
      g.1 ≫ eqToHom (if_pos hX).symm
  else 0

/-- The top-supported components defining a map out of `concentrated B k` are natural. -/
@[stacks 0190 "map from a concentrated object component naturality"]
theorem FaceMap.toHomApp.naturality {k : ℕ} {B : A}
    {V : SimplicialObject.Truncated A k} (g : FaceMap B V)
    {X Y : (SimplexCategory.Truncated k)ᵒᵖ} (φ : X ⟶ Y) :
    (concentrated B k).map φ ≫ g.toHomApp Y =
      g.toHomApp X ≫ V.map φ := sorry

/-- The top-supported components defining a map into `concentrated B k` are natural. -/
@[stacks 0190 "map to a concentrated object component naturality"]
theorem DegeneracyMap.toHomApp.naturality {k : ℕ} {B : A}
    {V : SimplicialObject.Truncated A k} (g : DegeneracyMap V B)
    {X Y : (SimplexCategory.Truncated k)ᵒᵖ} (φ : X ⟶ Y) :
    V.map φ ≫ g.toHomApp Y =
      g.toHomApp X ≫ (concentrated B k).map φ := sorry

/-- The top-supported components of a `FaceMap` assemble to a natural transformation. -/
@[stacks 0190 "map from a concentrated object"]
noncomputable def FaceMap.toHom {k : ℕ} {B : A}
    {V : SimplicialObject.Truncated A k}
    (g : FaceMap B V) :
    concentrated B k ⟶ V where
  app X := g.toHomApp X
  naturality _ _ φ := FaceMap.toHomApp.naturality g φ

/-- The top-supported components of a `DegeneracyMap` assemble to a natural transformation. -/
@[stacks 0190 "map to a concentrated object"]
noncomputable def DegeneracyMap.toHom {k : ℕ} {B : A}
    {V : SimplicialObject.Truncated A k}
    (g : DegeneracyMap V B) :
    V ⟶ concentrated B k where
  app X := g.toHomApp X
  naturality _ _ φ := DegeneracyMap.toHomApp.naturality g φ

/-- The bundled map out of a concentrated object has component `FaceMap.toHomApp`. -/
@[simp, stacks 0190 "map from a concentrated object component formula"]
theorem FaceMap.toHom_app {k : ℕ} {B : A} {V : SimplicialObject.Truncated A k}
    (g : FaceMap B V)
    (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    g.toHom.app X = g.toHomApp X := sorry

/-- The bundled map into a concentrated object has component `DegeneracyMap.toHomApp`. -/
@[simp, stacks 0190 "map to a concentrated object component formula"]
theorem DegeneracyMap.toHom_app {k : ℕ} {B : A}
    {V : SimplicialObject.Truncated A k}
    (g : DegeneracyMap V B)
    (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    g.toHom.app X = g.toHomApp X := sorry

/-- At top degree, reconstruction from face-compatible data is the supplied map after the
canonical comparison with the concentrated top value. -/
@[simp, stacks 0190 "map from a concentrated object top component"]
theorem FaceMap.toHom_app_top {k : ℕ} {B : A}
    {V : SimplicialObject.Truncated A k}
    (g : FaceMap B V) :
    g.toHom.app (op (top k)) = (topIso B k).inv ≫ g.1 := sorry

/-- At top degree, reconstruction from degeneracy-compatible data is the supplied map followed
by the canonical comparison with the concentrated top value. -/
@[simp, stacks 0190 "map to a concentrated object top component"]
theorem DegeneracyMap.toHom_app_top {k : ℕ} {B : A}
    {V : SimplicialObject.Truncated A k}
    (g : DegeneracyMap V B) :
    g.toHom.app (op (top k)) = g.1 ≫ (topIso B k).hom := sorry

/-- The top component extracted from a map out of a concentrated object satisfies the face
condition. -/
@[stacks 0190 "map from a concentrated object top-data condition"]
theorem FaceCondition.ofHom {k : ℕ} {B : A}
    {V : SimplicialObject.Truncated A k} (f : concentrated B k ⟶ V) :
    FaceCondition V ((topIso B k).hom ≫ f.app (op (top k))) := sorry

/-- Extract the top component and its face condition from a map out of a concentrated object. -/
@[stacks 0190 "map from a concentrated object to top data"]
noncomputable def FaceMap.ofHom {k : ℕ} {B : A}
    {V : SimplicialObject.Truncated A k} (f : concentrated B k ⟶ V) :
    FaceMap B V :=
  ⟨(topIso B k).hom ≫ f.app (op (top k)), FaceCondition.ofHom f⟩

/-- The top component extracted from a map into a concentrated object satisfies the degeneracy
condition. -/
@[stacks 0190 "map to a concentrated object top-data condition"]
theorem DegeneracyCondition.ofHom {k : ℕ} {B : A}
    {V : SimplicialObject.Truncated A k} (f : V ⟶ concentrated B k) :
    DegeneracyCondition V (f.app (op (top k)) ≫ (topIso B k).inv) := sorry

/-- Extract the top component and its degeneracy condition from a map into a concentrated
object. -/
@[stacks 0190 "map to a concentrated object to top data"]
noncomputable def DegeneracyMap.ofHom {k : ℕ} {B : A}
    {V : SimplicialObject.Truncated A k} (f : V ⟶ concentrated B k) :
    DegeneracyMap V B :=
  ⟨f.app (op (top k)) ≫ (topIso B k).inv, DegeneracyCondition.ofHom f⟩

/-- Reconstructing a map out of a concentrated object from its top data is the identity. -/
@[stacks 0190 "map from a concentrated object classification left inverse"]
theorem homFromEquiv.left_inv {k : ℕ} {B : A}
    {V : SimplicialObject.Truncated A k} (f : concentrated B k ⟶ V) :
    (FaceMap.ofHom f).toHom = f := sorry

/-- Extracting top data after reconstruction is the identity for face-compatible maps. -/
@[stacks 0190 "map from a concentrated object classification right inverse"]
theorem homFromEquiv.right_inv {k : ℕ} {B : A}
    {V : SimplicialObject.Truncated A k} (g : FaceMap B V) :
    FaceMap.ofHom g.toHom = g := sorry

/-- Reconstructing a map into a concentrated object from its top data is the identity. -/
@[stacks 0190 "map to a concentrated object classification left inverse"]
theorem homToEquiv.left_inv {k : ℕ} {B : A}
    {V : SimplicialObject.Truncated A k} (f : V ⟶ concentrated B k) :
    (DegeneracyMap.ofHom f).toHom = f := sorry

/-- Extracting top data after reconstruction is the identity for degeneracy-compatible maps. -/
@[stacks 0190 "map to a concentrated object classification right inverse"]
theorem homToEquiv.right_inv {k : ℕ} {B : A}
    {V : SimplicialObject.Truncated A k} (g : DegeneracyMap V B) :
    DegeneracyMap.ofHom g.toHom = g := sorry

/-- Maps from `concentrated B k` are face-compatible maps from `B` to the top degree. -/
@[stacks 0190]
noncomputable def homFromEquiv {k : ℕ} (B : A) (V : SimplicialObject.Truncated A k) :
    (concentrated B k ⟶ V) ≃ FaceMap B V where
  toFun := FaceMap.ofHom
  invFun := FaceMap.toHom
  left_inv := homFromEquiv.left_inv
  right_inv := homFromEquiv.right_inv

/-- Maps to `concentrated B k` are degeneracy-compatible maps from the top degree to `B`. -/
@[stacks 0190]
noncomputable def homToEquiv {k : ℕ} (B : A) (V : SimplicialObject.Truncated A k) :
    (V ⟶ concentrated B k) ≃ DegeneracyMap V B where
  toFun := DegeneracyMap.ofHom
  invFun := DegeneracyMap.toHom
  left_inv := homToEquiv.left_inv
  right_inv := homToEquiv.right_inv

/-- Evaluating `homFromEquiv` reads off the top component. -/
@[simp, stacks 0190 "map from a concentrated object classifier formula"]
theorem homFromEquiv.apply {k : ℕ} (B : A)
    (V : SimplicialObject.Truncated A k) (f : concentrated B k ⟶ V) :
    (homFromEquiv B V f).1 = (topIso B k).hom ≫ f.app (op (top k)) := sorry

/-- Evaluating `homToEquiv` reads off the top component. -/
@[simp, stacks 0190 "map to a concentrated object classifier formula"]
theorem homToEquiv.apply {k : ℕ} (B : A)
    (V : SimplicialObject.Truncated A k) (f : V ⟶ concentrated B k) :
    (homToEquiv B V f).1 = f.app (op (top k)) ≫ (topIso B k).inv := sorry

/-- The inverse of `homFromEquiv` has the explicit top-supported component formula. -/
@[stacks 0190 "map from a concentrated object inverse component formula"]
theorem homFromEquiv.symm_apply_app {k : ℕ} (B : A)
    (V : SimplicialObject.Truncated A k) (g : FaceMap B V)
    (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    ((homFromEquiv B V).symm g).app X = g.toHomApp X := sorry

/-- The inverse of `homToEquiv` has the explicit top-supported component formula. -/
@[stacks 0190 "map to a concentrated object inverse component formula"]
theorem homToEquiv.symm_apply_app {k : ℕ} (B : A)
    (V : SimplicialObject.Truncated A k) (g : DegeneracyMap V B)
    (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    ((homToEquiv B V).symm g).app X = g.toHomApp X := sorry

/-- `homFromEquiv` intertwines source precomposition with `FaceMap.precomp`. -/
@[simp, stacks 0190 "map-from classification source naturality"]
theorem homFromEquiv.precomp {k : ℕ} {B B' : A}
    {V : SimplicialObject.Truncated A k} (g : B' ⟶ B)
    (f : concentrated B k ⟶ V) :
    homFromEquiv B' V (map k g ≫ f) = (homFromEquiv B V f).precomp g := sorry

/-- `homFromEquiv` intertwines target postcomposition with `FaceMap.postcomp`. -/
@[simp, stacks 0190 "map-from classification target naturality"]
theorem homFromEquiv.postcomp {k : ℕ} {B : A}
    {V W : SimplicialObject.Truncated A k} (f : concentrated B k ⟶ V)
    (g : V ⟶ W) :
    homFromEquiv B W (f ≫ g) = (homFromEquiv B V f).postcomp g := sorry

/-- Reconstruction by `homFromEquiv.symm` respects source precomposition. -/
@[stacks 0190 "map-from reconstruction source naturality"]
theorem homFromEquiv.symm_precomp {k : ℕ} {B B' : A}
    {V : SimplicialObject.Truncated A k} (f : FaceMap B V) (g : B' ⟶ B) :
    (homFromEquiv B' V).symm (f.precomp g) =
      map k g ≫ (homFromEquiv B V).symm f := sorry

/-- Reconstruction by `homFromEquiv.symm` respects target postcomposition. -/
@[stacks 0190 "map-from reconstruction target naturality"]
theorem homFromEquiv.symm_postcomp {k : ℕ} {B : A}
    {V W : SimplicialObject.Truncated A k} (f : FaceMap B V) (g : V ⟶ W) :
    (homFromEquiv B W).symm (f.postcomp g) =
      (homFromEquiv B V).symm f ≫ g := sorry

/-- `homToEquiv` intertwines source precomposition with `DegeneracyMap.precomp`. -/
@[simp, stacks 0190 "map-to classification source naturality"]
theorem homToEquiv.precomp {k : ℕ} {B : A}
    {V W : SimplicialObject.Truncated A k} (g : V ⟶ W)
    (f : W ⟶ concentrated B k) :
    homToEquiv B V (g ≫ f) = (homToEquiv B W f).precomp g := sorry

/-- `homToEquiv` intertwines target postcomposition with `DegeneracyMap.postcomp`. -/
@[simp, stacks 0190 "map-to classification target naturality"]
theorem homToEquiv.postcomp {k : ℕ} {B B' : A}
    {V : SimplicialObject.Truncated A k} (f : V ⟶ concentrated B k)
    (g : B ⟶ B') :
    homToEquiv B' V (f ≫ map k g) = (homToEquiv B V f).postcomp g := sorry

/-- Reconstruction by `homToEquiv.symm` respects source precomposition. -/
@[stacks 0190 "map-to reconstruction source naturality"]
theorem homToEquiv.symm_precomp {k : ℕ} {B : A}
    {V W : SimplicialObject.Truncated A k} (f : DegeneracyMap W B) (g : V ⟶ W) :
    (homToEquiv B V).symm (f.precomp g) =
      g ≫ (homToEquiv B W).symm f := sorry

/-- Reconstruction by `homToEquiv.symm` respects target postcomposition. -/
@[stacks 0190 "map-to reconstruction target naturality"]
theorem homToEquiv.symm_postcomp {k : ℕ} {B B' : A}
    {V : SimplicialObject.Truncated A k} (f : DegeneracyMap V B) (g : B ⟶ B') :
    (homToEquiv B' V).symm (f.postcomp g) =
      (homToEquiv B V).symm f ≫ map k g := sorry

/-- A morphism out of `concentrated B k` is determined by its top component. -/
@[ext, stacks 0190 "map from a concentrated object extensionality"]
theorem homFromEquiv.hom_ext {k : ℕ} {B : A} {V : SimplicialObject.Truncated A k}
    {f g : concentrated B k ⟶ V}
    (h : f.app (op (top k)) = g.app (op (top k))) : f = g := sorry

/-- A morphism into `concentrated B k` is determined by its top component. -/
@[ext, stacks 0190 "map to a concentrated object extensionality"]
theorem homToEquiv.hom_ext {k : ℕ} {B : A} {V : SimplicialObject.Truncated A k}
    {f g : V ⟶ concentrated B k}
    (h : f.app (op (top k)) = g.app (op (top k))) : f = g := sorry

end concentrated

end CategoryTheory.SimplicialObject.Truncated
