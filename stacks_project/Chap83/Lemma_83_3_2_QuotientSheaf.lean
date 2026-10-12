/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf.Descent

/-!
# Quotient sheaves of pre-relations on algebraic spaces

This chapter-facing module retains the established universe-raised sheaf names
as aliases for the canonical algebraic-space sheaf API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The fppf sheaf of points of an algebraic space, with raised universe. -/
abbrev uliftSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  toSheaf.obj X

/-- The sheaf property of the universe-raised sheaf of points. -/
theorem uliftSheaf_isSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (X.functorOfPoints ⋙ uliftFunctor.{u + 1, u}) :=
  toSheaf_isSheaf X

/-- The underlying presheaf of the universe-raised sheaf of points. -/
theorem uliftSheaf_obj {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (uliftSheaf X).obj = X.functorOfPoints ⋙ uliftFunctor.{u + 1, u} :=
  toSheaf_obj X

/-- The sheaf morphism induced by a morphism of algebraic spaces. -/
abbrev uliftSheafMap {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    uliftSheaf X ⟶ uliftSheaf Y :=
  toSheaf.map f

/-- The underlying presheaf morphism of `uliftSheafMap f`. -/
theorem uliftSheafMap_hom {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (uliftSheafMap f).hom = Functor.whiskerRight f uliftFunctor.{u + 1, u} :=
  toSheaf_map f

end AlgebraicGeometry.AlgebraicSpace
