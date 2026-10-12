/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.AugmentationFunctor
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.TotalFunctor.Preadditive

/-!
# Additive source functors for Cartan--Eilenberg augmentations

The source complexes occurring in raw and mapped augmentation transformations inherit canonical
additive structures.  Registering them here keeps augmentation arguments free of local instance
reconstruction.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Bundled

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]

namespace Total

/-- The raw augmentation source-complex functor is additive. -/
@[stacks 015J "additivity of the raw augmentation source functor"]
noncomputable instance sourceComplex_additive :
    (sourceComplex : Bundled A ⥤ CochainComplex A ℤ).Additive := sorry

/-- The raw augmentation source functor preserves zero maps. -/
@[simp]
theorem sourceComplex_map_zero {X Y : Bundled A} :
    sourceComplex.map (0 : X ⟶ Y) = 0 := sorry

/-- The raw augmentation source functor preserves sums of maps. -/
@[simp]
theorem sourceComplex_map_add {X Y : Bundled A} (f g : X ⟶ Y) :
    sourceComplex.map (f + g) = sourceComplex.map f + sourceComplex.map g := sorry

/-- The raw augmentation source functor preserves additive inverses. -/
@[simp]
theorem sourceComplex_map_neg {X Y : Bundled A} (f : X ⟶ Y) :
    sourceComplex.map (-f) = -sourceComplex.map f := sorry

/-- The raw augmentation source functor preserves subtraction. -/
@[simp]
theorem sourceComplex_map_sub {X Y : Bundled A} (f g : X ⟶ Y) :
    sourceComplex.map (f - g) = sourceComplex.map f - sourceComplex.map g := sorry

/-- The raw augmentation source functor preserves natural-number scalar multiplication. -/
theorem sourceComplex_map_nsmul {X Y : Bundled A} (n : ℕ) (f : X ⟶ Y) :
    sourceComplex.map (n • f) = n • sourceComplex.map f := sorry

/-- The raw augmentation source functor preserves integer scalar multiplication. -/
theorem sourceComplex_map_zsmul {X Y : Bundled A} (n : ℤ) (f : X ⟶ Y) :
    sourceComplex.map (n • f) = n • sourceComplex.map f := sorry

end Total

namespace MappedTotal

variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- The mapped augmentation source-complex functor is additive. -/
@[stacks 015J "additivity of the mapped augmentation source functor"]
noncomputable instance sourceComplex_additive (F : A ⥤ B) [F.Additive] :
    (sourceComplex F).Additive := sorry

/-- The mapped augmentation source functor preserves zero maps. -/
@[simp]
theorem sourceComplex_map_zero (F : A ⥤ B) [F.Additive] {X Y : Bundled A} :
    (sourceComplex F).map (0 : X ⟶ Y) = 0 := sorry

/-- The mapped augmentation source functor preserves sums of maps. -/
@[simp]
theorem sourceComplex_map_add (F : A ⥤ B) [F.Additive]
    {X Y : Bundled A} (f g : X ⟶ Y) :
    (sourceComplex F).map (f + g) =
      (sourceComplex F).map f + (sourceComplex F).map g := sorry

/-- The mapped augmentation source functor preserves additive inverses. -/
@[simp]
theorem sourceComplex_map_neg (F : A ⥤ B) [F.Additive]
    {X Y : Bundled A} (f : X ⟶ Y) :
    (sourceComplex F).map (-f) = -(sourceComplex F).map f := sorry

/-- The mapped augmentation source functor preserves subtraction. -/
@[simp]
theorem sourceComplex_map_sub (F : A ⥤ B) [F.Additive]
    {X Y : Bundled A} (f g : X ⟶ Y) :
    (sourceComplex F).map (f - g) =
      (sourceComplex F).map f - (sourceComplex F).map g := sorry

/-- The mapped augmentation source functor preserves natural-number scalar multiplication. -/
theorem sourceComplex_map_nsmul (F : A ⥤ B) [F.Additive]
    {X Y : Bundled A} (n : ℕ) (f : X ⟶ Y) :
    (sourceComplex F).map (n • f) = n • (sourceComplex F).map f := sorry

/-- The mapped augmentation source functor preserves integer scalar multiplication. -/
theorem sourceComplex_map_zsmul (F : A ⥤ B) [F.Additive]
    {X Y : Bundled A} (n : ℤ) (f : X ⟶ Y) :
    (sourceComplex F).map (n • f) = n • (sourceComplex F).map f := sorry

end MappedTotal

#synth (Total.sourceComplex (A := A)).Additive

end CochainComplex.CartanEilenbergResolution.Bundled
