/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Product
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Object

/-!
# Separation properties of quotient stacks

For a flat, locally finitely presented groupoid in algebraic spaces whose quotient
is algebraic, properties of the relation map or the source and target maps imply
separation properties of the quotient. All products, diagonals, and separation
properties are relative to the fixed base scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry GroupoidAlgebraicSpace Limits
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The diagonal of the algebraic quotient of a flat, locally finitely presented
groupoid is separated over the base scheme if its relation map is separated. -/
theorem has_separated_diagonal {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    [AlgebraicStack (SmallQuotient.quotientStack G)]
    [AlgebraicSpace.Separated (prod.lift G.t.left G.s.left)] :
    Groupoids.Hom.has (@AlgebraicSpace.Separated S)
      (diagonal.{u + 1, u, u + 1} (SmallQuotient.quotientStack G)) := sorry

/-- The diagonal of the algebraic quotient of a flat, locally finitely presented
groupoid is separated over the base scheme if its object and arrow spaces are separated. -/
theorem has_separated_diagonal_of_isSeparated {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    [AlgebraicStack (SmallQuotient.quotientStack G)] [AlgebraicSpace.IsSeparated G.U.left]
    [AlgebraicSpace.IsSeparated G.R.left] :
    Groupoids.Hom.has (@AlgebraicSpace.Separated S)
      (diagonal.{u + 1, u, u + 1} (SmallQuotient.quotientStack G)) := sorry

/-- The algebraic quotient of a flat, locally finitely presented groupoid is
quasi-DM over the base scheme if its relation map is locally quasi-finite. -/
theorem isQuasiDMOver_of_locallyQuasiFinite_j {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) [Flat G]
    [LocallyOfFinitePresentation G] [AlgebraicStack (SmallQuotient.quotientStack G)]
    [AlgebraicSpace.LocallyQuasiFinite (prod.lift G.t.left G.s.left)] :
    AlgebraicStack.IsQuasiDMOver (SmallQuotient.quotientStack G) := sorry

/-- The algebraic quotient of a flat, locally finitely presented groupoid is
quasi-DM over the base scheme if its source and target maps are locally quasi-finite. -/
theorem isQuasiDMOver_of_locallyQuasiFinite {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) [Flat G]
    [LocallyOfFinitePresentation G] [AlgebraicStack (SmallQuotient.quotientStack G)]
    [AlgebraicSpace.LocallyQuasiFinite G.s.left]
    [AlgebraicSpace.LocallyQuasiFinite G.t.left] :
    AlgebraicStack.IsQuasiDMOver (SmallQuotient.quotientStack G) := sorry

/-- The algebraic quotient of a flat, locally finitely presented groupoid is
separated over the base scheme if its relation map is proper. -/
theorem isSeparatedOver_of_proper_j {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    [AlgebraicStack (SmallQuotient.quotientStack G)]
    [AlgebraicSpace.Proper (prod.lift G.t.left G.s.left)] :
    AlgebraicStack.IsSeparatedOver (SmallQuotient.quotientStack G) := sorry

/-- The algebraic quotient of a flat, locally finitely presented groupoid is
separated over the base scheme if its source and target maps are proper and
its object space is separated. -/
theorem isSeparatedOver_of_proper {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    [AlgebraicStack (SmallQuotient.quotientStack G)] [AlgebraicSpace.Proper G.s.left]
    [AlgebraicSpace.Proper G.t.left] [AlgebraicSpace.IsSeparated G.U.left] :
    AlgebraicStack.IsSeparatedOver (SmallQuotient.quotientStack G) := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
