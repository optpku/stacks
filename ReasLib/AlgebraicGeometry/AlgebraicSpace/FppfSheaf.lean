module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import Mathlib.CategoryTheory.Whiskering

/-! # Universe-raised fppf sheaves of points of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Universe-raised functor of points of an algebraic space, as an fppf sheaf. -/
theorem toFppfSheaf_isSheaf (S : Scheme.{u}) (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (X.functorOfPoints ⋙ uliftFunctor.{u + 1, u}) :=
  sorry

/-- The functor sending an algebraic space over `S` to its universe-raised fppf sheaf
of points. -/
def toFppfSheaf (S : Scheme.{u}) :
    AlgebraicSpace S ⥤ Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) where
  obj X := ⟨X.functorOfPoints ⋙ uliftFunctor.{u + 1, u}, toFppfSheaf_isSheaf S X⟩
  map f := ObjectProperty.homMk (Functor.whiskerRight f uliftFunctor.{u + 1, u})

/-- The underlying presheaf of `(toFppfSheaf S).obj X` is the universe-raised functor of
points. -/
theorem toFppfSheaf_obj (S : Scheme.{u}) (X : AlgebraicSpace S) :
    ((toFppfSheaf S).obj X).obj = X.functorOfPoints ⋙ uliftFunctor.{u + 1, u} :=
  sorry

/-- The action of `toFppfSheaf S` on morphisms is universe-raising of the transformation of
functors of points. -/
theorem toFppfSheaf_map (S : Scheme.{u}) {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ((toFppfSheaf S).map f).hom = Functor.whiskerRight f uliftFunctor.{u + 1, u} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
