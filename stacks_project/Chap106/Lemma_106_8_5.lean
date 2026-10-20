module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FormallySmooth.Representable
import StacksCheckRecall

/-!
# Formally smooth morphisms representable by algebraic spaces

A morphism of algebraic stacks representable by algebraic spaces is formally
smooth if and only if every scheme-slice base change is formally smooth as a
morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 106.8.5. A morphism of algebraic stacks representable by algebraic
spaces is formally smooth if and only if every scheme-slice base change is
formally smooth as a morphism of algebraic spaces. -/
@[stacks 0H1K] #check (AlgebraicGeometry.AlgebraicStack.FormallySmooth.iff_has :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f),
    FormallySmooth f ↔ Groupoids.Hom.has (@AlgebraicSpace.FormallySmooth S) f)

#check (AlgebraicGeometry.AlgebraicStack.FormallySmooth.iff_represents :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f),
    FormallySmooth f ↔
      ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
        (fy : Fy ⟶ AlgebraicSpace.ofOver U),
        RepresentsBaseChange f y Fy fy → AlgebraicSpace.FormallySmooth fy)

#check (AlgebraicGeometry.AlgebraicStack.FormallySmooth.spec_represents :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [FormallySmooth f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U} (h : RepresentsBaseChange f y Fy fy),
    AlgebraicSpace.FormallySmooth fy)

#check (AlgebraicGeometry.AlgebraicStack.FormallySmooth.of_has :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (h : Groupoids.Hom.has (@AlgebraicSpace.FormallySmooth S) f),
    FormallySmooth f)

end AlgebraicGeometry.AlgebraicStack
