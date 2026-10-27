/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Separation
import StacksCheckRecall

/-!
# Separation properties of a quotient stack from its presentation

For a groupoid in algebraic spaces with flat, locally finitely presented source
and target and an algebraic quotient stack, the six presentation criteria below
give a separated diagonal, a quasi-DM quotient, or a separated quotient.
Products, diagonals, and separatedness are relative to the fixed scheme `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry GroupoidAlgebraicSpace Limits
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/- Lemma 101.20.1 (1): If the relation map is separated, the quotient diagonal is separated. -/
@[stacks 0DTY] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.has_separated_diagonal :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    [AlgebraicStack (SmallQuotient.quotientStack G)]
    [AlgebraicSpace.Separated (prod.lift G.t.left G.s.left)],
    Groupoids.Hom.has (@AlgebraicSpace.Separated S)
      (diagonal.{u + 1, u, u + 1} (SmallQuotient.quotientStack G)))

/- Lemma 101.20.1 (2): If the object and arrow spaces are separated, the quotient diagonal is separated. -/
@[stacks 0DTY] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.has_separated_diagonal_of_isSeparated :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    [AlgebraicStack (SmallQuotient.quotientStack G)] [AlgebraicSpace.IsSeparated G.U.left]
    [AlgebraicSpace.IsSeparated G.R.left],
    Groupoids.Hom.has (@AlgebraicSpace.Separated S)
      (diagonal.{u + 1, u, u + 1} (SmallQuotient.quotientStack G)))

/- Lemma 101.20.1 (3): If the relation map is locally quasi-finite, the quotient is quasi-DM. -/
@[stacks 0DTY] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.isQuasiDMOver_of_locallyQuasiFinite_j :
    ∀ {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) [Flat G]
    [LocallyOfFinitePresentation G] [AlgebraicStack (SmallQuotient.quotientStack G)]
    [AlgebraicSpace.LocallyQuasiFinite (prod.lift G.t.left G.s.left)],
    AlgebraicStack.IsQuasiDMOver (SmallQuotient.quotientStack G))

/- Lemma 101.20.1 (4): If the source and target maps are locally quasi-finite, the quotient is quasi-DM. -/
@[stacks 0DTY] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.isQuasiDMOver_of_locallyQuasiFinite :
    ∀ {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) [Flat G]
    [LocallyOfFinitePresentation G] [AlgebraicStack (SmallQuotient.quotientStack G)]
    [AlgebraicSpace.LocallyQuasiFinite G.s.left]
    [AlgebraicSpace.LocallyQuasiFinite G.t.left],
    AlgebraicStack.IsQuasiDMOver (SmallQuotient.quotientStack G))

/- Lemma 101.20.1 (5): If the relation map is proper, the quotient is separated. -/
@[stacks 0DTY] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.isSeparatedOver_of_proper_j :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    [AlgebraicStack (SmallQuotient.quotientStack G)]
    [AlgebraicSpace.Proper (prod.lift G.t.left G.s.left)],
    AlgebraicStack.IsSeparatedOver (SmallQuotient.quotientStack G))

/- Lemma 101.20.1 (6): If the source and target maps are proper and the object space is separated,
the quotient is separated. -/
@[stacks 0DTY] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.isSeparatedOver_of_proper :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    [AlgebraicStack (SmallQuotient.quotientStack G)] [AlgebraicSpace.Proper G.s.left]
    [AlgebraicSpace.Proper G.t.left] [AlgebraicSpace.IsSeparated G.U.left],
    AlgebraicStack.IsSeparatedOver (SmallQuotient.quotientStack G))

end AlgebraicGeometry.GroupoidAlgebraicSpace
