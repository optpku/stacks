module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

universe u v

namespace CategoryTheory

/-- A Frobenius crystal for an endofunctor `F` consists of an object and a
morphism from its image under `F` to itself. -/
structure FrobeniusCrystal {C : Type u} [Category.{v} C] (F : C ⥤ C) where
  /-- The underlying object. -/
  obj : C
  /-- The Frobenius morphism from the endofunctor image to the underlying object. -/
  frobenius : F.obj obj ⟶ obj

namespace FrobeniusCrystal

/-- Construct a Frobenius crystal from an object and its Frobenius morphism. -/
def of {C : Type u} [Category.{v} C] (F : C ⥤ C)
    (object : C) (frobenius : F.obj object ⟶ object) : FrobeniusCrystal F :=
  { obj := object, frobenius := frobenius }

/-- A Frobenius crystal is nondegenerate at a prime `p` when a morphism back to
its endofunctor image composes with Frobenius to a nonnegative power of `p`
times the identity of that image. -/
def IsNondegenerate {C : Type u} [Category.{v} C] [Preadditive C]
    {F : C ⥤ C} (p : ℕ) [Fact (Nat.Prime p)] (𝓔 : FrobeniusCrystal F) : Prop :=
  ∃ i : ℕ, ∃ V : 𝓔.obj ⟶ F.obj 𝓔.obj,
    𝓔.frobenius ≫ V = (p ^ i) • 𝟙 (F.obj 𝓔.obj)

end FrobeniusCrystal

end CategoryTheory
