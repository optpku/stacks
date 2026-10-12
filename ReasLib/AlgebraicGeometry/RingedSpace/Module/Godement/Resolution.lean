/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Godement.Step
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Zero
public import ReasLib.AlgebraicTopology.CosimplicialObject.Augmented.AlternatingCoface
public import ReasLib.CategoryTheory.Endofunctor.MonadResolution.Evaluation

/-!
# The functorial Godement resolution

The Godement monad produces an augmented cosimplicial module sheaf whose degree `n` is the
`(n + 1)`-fold Godement step.  Passing to the alternating-coface complex gives the canonical
functorial Godement complex and its augmentation from degree zero.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology
open scoped AlgebraicGeometry CategoryTheory.IteratedEndofunctor Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Godement

/-- The augmented cosimplicial Godement resolution, functorial in the module sheaf. -/
@[stacks 0FKS "augmented cosimplicial Godement resolution"]
noncomputable abbrev augmented (X : RingedSpace.{u}) :
    X.Modules ⥤ CosimplicialObject.Augmented X.Modules :=
  CategoryTheory.Monad.cosimplicialResolution.eval (monad X)

/-- The cosimplicial part of the Godement resolution. -/
@[stacks 0FKS "cosimplicial Godement resolution"]
noncomputable abbrev cosimplicial (X : RingedSpace.{u}) :
    X.Modules ⥤ CosimplicialObject X.Modules :=
  augmented X ⋙ CosimplicialObject.Augmented.drop

/-- The ordinary Godement cochain complex obtained from alternating cofaces. -/
@[stacks 0FKS "Godement cochain complex"]
noncomputable abbrev complex (X : RingedSpace.{u}) :
    X.Modules ⥤ CochainComplex X.Modules ℕ :=
  cosimplicial X ⋙ alternatingCofaceMapComplex X.Modules

/-- The component of the Godement augmentation at a module sheaf. -/
@[stacks 0FKS "Godement complex augmentation component"]
noncomputable def augmentationApp (X : RingedSpace.{u}) (ℱ : X.Modules) :
    (CochainComplex.single₀ X.Modules).obj ℱ ⟶ (complex X).obj ℱ :=
  AlternatingCofaceMapComplex.coaugmentationApp ((augmented X).obj ℱ)

/-- Naturality of the objectwise Godement augmentations. -/
@[stacks 0FKS "naturality of the Godement complex augmentation"]
theorem augmentationApp_naturality (X : RingedSpace.{u})
    {ℱ 𝒢 : X.Modules} (f : ℱ ⟶ 𝒢) :
    (CochainComplex.single₀ X.Modules).map f ≫ augmentationApp X 𝒢 =
      augmentationApp X ℱ ≫ (complex X).map f := sorry

/-- The functorial augmentation from module sheaves in degree zero to their Godement complexes. -/
@[stacks 0FKS "functorial Godement complex augmentation"]
noncomputable def augmentation (X : RingedSpace.{u}) :
    CochainComplex.single₀ X.Modules ⟶ complex X where
  app := augmentationApp X
  naturality := fun _ _ f ↦ augmentationApp_naturality X f

/-- The augmentation point of the evaluated Godement resolution is the original module sheaf. -/
@[simp]
theorem augmented_obj_left (X : RingedSpace.{u}) (ℱ : X.Modules) :
    ((augmented X).obj ℱ).left = ℱ := sorry

/-- Cosimplicial degree `n` of the Godement resolution is the `(n + 1)`-fold Godement step. -/
@[stacks 0FKS "terms of the cosimplicial Godement resolution"]
theorem cosimplicial_obj (X : RingedSpace.{u}) (ℱ : X.Modules) (n : ℕ) :
    ((cosimplicial X).obj ℱ).obj (SimplexCategory.mk n) =
      ((step X) ⁺⦋n⦌).obj ℱ := sorry

/-- Degree `n` of the Godement complex is the `(n + 1)`-fold Godement step. -/
@[stacks 0FKS "terms of the Godement complex"]
theorem complex_obj_X (X : RingedSpace.{u}) (ℱ : X.Modules) (n : ℕ) :
    ((complex X).obj ℱ).X n = ((step X) ⁺⦋n⦌).obj ℱ := sorry

/-- Degree zero of the Godement complex is one Godement step. -/
@[stacks 0FKS "degree-zero term of the Godement complex"]
theorem complex_obj_X_zero (X : RingedSpace.{u}) (ℱ : X.Modules) :
    ((complex X).obj ℱ).X 0 = (step X).obj ℱ := sorry

/-- The degree-zero component of the Godement augmentation is the Godement unit. -/
@[simp, stacks 0FKS "degree-zero Godement augmentation"]
theorem augmentation_app_f_zero (X : RingedSpace.{u}) (ℱ : X.Modules) :
    ((augmentation X).app ℱ).f 0 = (unit X).app ℱ := sorry

/-- Every positive-degree component of the Godement augmentation is zero. -/
@[simp]
theorem augmentation_app_f_succ (X : RingedSpace.{u}) (ℱ : X.Modules) (n : ℕ) :
    ((augmentation X).app ℱ).f (n + 1) = 0 := sorry

/-- In degree `n`, the Godement complex map induced by `f` is the `(n + 1)`-fold iterated
Godement-step map. -/
@[stacks 0FKS "maps of the Godement complex"]
theorem complex_map_f (X : RingedSpace.{u}) {ℱ 𝒢 : X.Modules}
    (f : ℱ ⟶ 𝒢) (n : ℕ) :
    ((complex X).map f).f n = ((step X) ⁺⦋n⦌).map f := sorry

end AlgebraicGeometry.RingedSpace.Godement
