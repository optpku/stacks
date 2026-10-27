/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Flat
import StacksCheckRecall

/-!
# Atlas of a flat locally finitely presented groupoid

If `(U, R, s, t, c)` is a groupoid in algebraic spaces whose source and
target maps are flat and locally of finite presentation, then the atlas
`SmallQuotient.atlas G : G.U.left.toGroupoids ⟶ SmallQuotient.quotientStack G`
is flat, locally of finite presentation, and surjective. This canonical atlas
is point inclusion followed by fppf stackification.

We retain the established universe convention: `S : Scheme.{u}` and the
quotient in the original Hom universe of `GroupoidsOver S`, with no additional
size assumption or universe lift. The groupoid is formalized over an algebraic
space `B` over `S`; forgetting its map to `B` gives a groupoid over `S`.
-/

open AlgebraicGeometry

universe u

/- Lemma 97.17.1 (1): the canonical atlas of a flat locally finitely presented
groupoid in algebraic spaces is flat. -/
@[stacks 06FH] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient.flat_atlas :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      (hFlat : GroupoidAlgebraicSpace.Flat G)
      (hLfp : GroupoidAlgebraicSpace.LocallyOfFinitePresentation G),
      Groupoids.Hom.Flat (GroupoidAlgebraicSpace.SmallQuotient.atlas G))

/- Lemma 97.17.1 (2): the canonical atlas of a flat locally finitely presented
groupoid in algebraic spaces is locally of finite presentation. -/
@[stacks 06FH] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient.locallyOfFinitePresentation_atlas :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      (hFlat : GroupoidAlgebraicSpace.Flat G)
      (hLfp : GroupoidAlgebraicSpace.LocallyOfFinitePresentation G),
      Groupoids.Hom.LocallyOfFinitePresentation
        (GroupoidAlgebraicSpace.SmallQuotient.atlas G))

/- Lemma 97.17.1 (3): the canonical atlas of a flat locally finitely presented
groupoid in algebraic spaces is surjective. -/
@[stacks 06FH] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient.surjective_atlas_of_flat :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      (hFlat : GroupoidAlgebraicSpace.Flat G)
      (hLfp : GroupoidAlgebraicSpace.LocallyOfFinitePresentation G),
      Groupoids.Hom.Surjective (GroupoidAlgebraicSpace.SmallQuotient.atlas G))
