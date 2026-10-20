module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms of algebraic-space fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` is
representable by algebraic spaces whenever both source and target are.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A 1-morphism between categories fibred in groupoids over `S` that are both
representable by algebraic spaces is representable by algebraic spaces. -/
@[stacks 02ZZ]
theorem relativelyRepresentableByAlgebraicSpaces.of_isRepresentableByAlgebraicSpace
    {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (hX : IsRepresentableByAlgebraicSpace X)
    (hY : IsRepresentableByAlgebraicSpace Y) :
    relativelyRepresentableByAlgebraicSpaces f := sorry

/-- The 1-morphism of groupoid fibrations associated to a morphism of algebraic
spaces over `S` is representable by algebraic spaces. -/
theorem relativelyRepresentableByAlgebraicSpaces.of_toGroupoids_map
    {S : Scheme.{u}} {F G : AlgebraicSpace S} (φ : F ⟶ G) :
    relativelyRepresentableByAlgebraicSpaces (AlgebraicSpace.toGroupoids.map φ) :=
  relativelyRepresentableByAlgebraicSpaces.of_isRepresentableByAlgebraicSpace
    (AlgebraicSpace.toGroupoids.map φ)
    (IsRepresentableByAlgebraicSpace.of_toGroupoids F)
    (IsRepresentableByAlgebraicSpace.of_toGroupoids G)

end AlgebraicGeometry
