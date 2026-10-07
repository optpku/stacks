module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.LinearAlgebra.Dual.Defs

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.SerreFunctor

variable {T : Type u} [Category.{v} T] [Preadditive T]

/-- Dualization of postcomposition, giving the map of `homDualRight`. -/
def homDualRightMap (k : Type w) [Field k] [Linear k T] (X : T)
    {Y Z : Tᵒᵖ} (f : Y ⟶ Z) :
    Module.Dual k (X ⟶ Y.unop) ⟶ Module.Dual k (X ⟶ Z.unop) :=
  ↾fun φ ↦ (CategoryTheory.Linear.rightComp k X f.unop).dualMap φ

/-- Dualization of postcomposition preserves identity morphisms. -/
theorem homDualRightMap_id (k : Type w) [Field k] [Linear k T]
    (X : T) (Y : Tᵒᵖ) :
    homDualRightMap k X (𝟙 Y) = 𝟙 (Module.Dual k (X ⟶ Y.unop)) := sorry

/-- Dualization of postcomposition preserves composition. -/
theorem homDualRightMap_comp (k : Type w) [Field k] [Linear k T]
    (X : T) {Y Z W : Tᵒᵖ} (f : Y ⟶ Z) (g : Z ⟶ W) :
    homDualRightMap k X (f ≫ g) =
      homDualRightMap k X f ≫ homDualRightMap k X g := sorry

/-- The contravariant functor `Y ↦ Module.Dual k (X ⟶ Y)` for a fixed object `X`. -/
def homDualRight (k : Type w) [Field k] [Linear k T] (X : T) :
    Tᵒᵖ ⥤ Type (max w v) where
  obj Y := Module.Dual k (X ⟶ Y.unop)
  map f := homDualRightMap k X f
  map_id Y := homDualRightMap_id k X Y
  map_comp f g := homDualRightMap_comp k X f g

/-- Dualization of precomposition, giving the map of `homDualLeft`. -/
def homDualLeftMap (k : Type w) [Field k] [Linear k T] (X : T)
    {Y Z : T} (f : Y ⟶ Z) :
    Module.Dual k (Y ⟶ X) ⟶ Module.Dual k (Z ⟶ X) :=
  ↾fun φ ↦ (CategoryTheory.Linear.leftComp k X f).dualMap φ

/-- Dualization of precomposition preserves identity morphisms. -/
theorem homDualLeftMap_id (k : Type w) [Field k] [Linear k T]
    (X Y : T) :
    homDualLeftMap k X (𝟙 Y) = 𝟙 (Module.Dual k (Y ⟶ X)) := sorry

/-- Dualization of precomposition preserves composition. -/
theorem homDualLeftMap_comp (k : Type w) [Field k] [Linear k T]
    (X : T) {Y Z W : T} (f : Y ⟶ Z) (g : Z ⟶ W) :
    homDualLeftMap k X (f ≫ g) =
      homDualLeftMap k X f ≫ homDualLeftMap k X g := sorry

/-- The covariant functor `Y ↦ Module.Dual k (Y ⟶ X)` for a fixed object `X`. -/
def homDualLeft (k : Type w) [Field k] [Linear k T] (X : T) :
    T ⥤ Type (max w v) where
  obj Y := Module.Dual k (Y ⟶ X)
  map f := homDualLeftMap k X f
  map_id Y := homDualLeftMap_id k X Y
  map_comp f g := homDualLeftMap_comp k X f g

end CategoryTheory.SerreFunctor

end
