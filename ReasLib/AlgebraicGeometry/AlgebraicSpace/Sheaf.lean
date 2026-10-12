/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Presentation

/-!
# Sheaves associated to algebraic spaces

This module records the presheaf and sheaf valued functors of points of an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The forgetful functor sending an algebraic space to its functor of points. -/
def forgetToPresheaf {S : Scheme.{u}} :
    AlgebraicSpace S ⥤ ((Over S)ᵒᵖ ⥤ Type u) where
  obj X := X.functorOfPoints
  map f := f

/-- The underlying presheaf of `forgetToPresheaf.obj X` is the functor of points. -/
theorem forgetToPresheaf_obj {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (forgetToPresheaf.obj X) = X.functorOfPoints :=
  rfl

/-- The action of `forgetToPresheaf` on morphisms is the identity on transformations. -/
theorem forgetToPresheaf_map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    forgetToPresheaf.map f = f :=
  rfl

/-- The functor of points of an algebraic space is a sheaf for the fppf topology. -/
theorem toSheaf_isSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (X.functorOfPoints ⋙ uliftFunctor.{u + 1, u}) :=
  sorry

/-- The functor sending an algebraic space to its universe-raised sheaf of points. -/
def toSheaf {S : Scheme.{u}} :
    AlgebraicSpace S ⥤ Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) where
  obj X := ⟨X.functorOfPoints ⋙ uliftFunctor.{u + 1, u}, toSheaf_isSheaf X⟩
  map f := ObjectProperty.homMk (Functor.whiskerRight f uliftFunctor.{u + 1, u})

/-- The underlying presheaf of `toSheaf.obj X` is the universe-raised functor of points. -/
theorem toSheaf_obj {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (toSheaf.obj X).obj = X.functorOfPoints ⋙ uliftFunctor.{u + 1, u} :=
  rfl

/-- The action of `toSheaf` on morphisms is universe-raising of the transformation. -/
theorem toSheaf_map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (toSheaf.map f).hom = Functor.whiskerRight f uliftFunctor.{u + 1, u} :=
  rfl

/-- The atlas of a presentation, viewed as a morphism of fppf sheaves. -/
def atlasToSheaf {S : Scheme.{u}} {F : AlgebraicSpace S} (P : Presentation F) :
    (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.obj P.U ⟶ toSheaf.obj F :=
  ObjectProperty.homMk (Functor.whiskerRight P.atlas uliftFunctor.{u + 1, u})

end AlgebraicGeometry.AlgebraicSpace
