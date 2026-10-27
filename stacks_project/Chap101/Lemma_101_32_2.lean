/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.OpenSubgroupoid
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 101.32.2 (1): The canonical morphism `[U / P] ⟶ [U / R]` is representable by algebraic spaces. -/
@[stacks 0DU2] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.OpenSubgroupoid.relativelyRepresentableByAlgebraicSpaces_quotientHom :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : AlgebraicGeometry.GroupoidAlgebraicSpace.OpenSubgroupoid G),
    AlgebraicGeometry.GroupoidAlgebraicSpace.Flat G → AlgebraicGeometry.GroupoidAlgebraicSpace.LocallyOfFinitePresentation G →
      relativelyRepresentableByAlgebraicSpaces H.quotientHom)

/- Lemma 101.32.2 (2): The canonical quotient morphism is surjective. -/
@[stacks 0DU2] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.OpenSubgroupoid.surjective_quotientHom :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : AlgebraicGeometry.GroupoidAlgebraicSpace.OpenSubgroupoid G),
    AlgebraicGeometry.GroupoidAlgebraicSpace.Flat G → AlgebraicGeometry.GroupoidAlgebraicSpace.LocallyOfFinitePresentation G →
      Groupoids.Hom.Surjective H.quotientHom)

/- Lemma 101.32.2 (3): The canonical quotient morphism is étale. -/
@[stacks 0DU2] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.OpenSubgroupoid.etale_quotientHom :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : AlgebraicGeometry.GroupoidAlgebraicSpace.OpenSubgroupoid G),
    AlgebraicGeometry.GroupoidAlgebraicSpace.Flat G → AlgebraicGeometry.GroupoidAlgebraicSpace.LocallyOfFinitePresentation G →
      Groupoids.Hom.Etale H.quotientHom)

/- Lemma 101.32.2 (4): The quotient `[U / P]` is an algebraic stack. -/
@[stacks 0DU2] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.OpenSubgroupoid.isAlgebraicStack_quotientStack :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : AlgebraicGeometry.GroupoidAlgebraicSpace.OpenSubgroupoid G),
    AlgebraicGeometry.GroupoidAlgebraicSpace.Flat G → AlgebraicGeometry.GroupoidAlgebraicSpace.LocallyOfFinitePresentation G →
      AlgebraicStack (AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient.quotientStack H.toGroupoid))

/- Lemma 101.32.2 (5): The ambient quotient `[U / R]` is an algebraic stack. -/
@[stacks 0DU2] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.isAlgebraicStack_quotientStack_of_flat :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      AlgebraicGeometry.GroupoidAlgebraicSpace.Flat G → AlgebraicGeometry.GroupoidAlgebraicSpace.LocallyOfFinitePresentation G →
        AlgebraicStack (AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient.quotientStack G))
