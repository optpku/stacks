module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Over

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-! The full subcategory of finite-type schemes over a Noetherian base. -/

/-- The full category of schemes of finite type over a Noetherian scheme `S`. -/
abbrev FiniteTypeOver (S : Scheme.{u}) [IsNoetherian S] :=
  ObjectProperty.FullSubcategory (fun X : Over S ↦ Hom.FiniteType X.hom)

namespace FiniteTypeOver

variable {S : Scheme.{u}} [IsNoetherian S]

/-- The structure morphism of an object of `FiniteTypeOver S` is of finite type. -/
theorem instFiniteType (X : FiniteTypeOver S) : Hom.FiniteType X.obj.hom := sorry

/-- The underlying scheme of an object of `FiniteTypeOver S` is Noetherian. -/
instance instIsNoetherian (X : FiniteTypeOver S) : IsNoetherian X.obj.left := sorry

/-- A morphism between schemes of finite type over a Noetherian base is of finite type. -/
theorem instFiniteTypeHom {X Y : FiniteTypeOver S} (f : X ⟶ Y) :
    Hom.FiniteType f.hom.left := sorry

/-- The object condition in `FiniteTypeOver S` is finite type of the structure morphism. -/
theorem condition (X : FiniteTypeOver S) : Hom.FiniteType X.obj.hom := sorry

/-- Morphisms in `FiniteTypeOver S` commute with the structure morphisms to `S`. -/
theorem hom_comm {X Y : FiniteTypeOver S} (f : X ⟶ Y) :
    f.hom.left ≫ Y.obj.hom = X.obj.hom := sorry

end FiniteTypeOver

end AlgebraicGeometry.Scheme
