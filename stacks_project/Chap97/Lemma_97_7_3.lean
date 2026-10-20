module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.SurjectiveOnObjects.Representable
import StacksCheckRecall

/-!
# Surjective on objects versus surjective morphisms of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is surjective on objects if and only if it is
surjective.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

universe u

/- Lemma 97.7.3: A 1-morphism of categories fibred in groupoids over
`(Sch/S)_fppf` that is representable by algebraic spaces is surjective on
objects if and only if it is surjective. -/
@[stacks 06D7] #check
  (AlgebraicGeometry.Groupoids.Hom.SurjectiveOnObjects.iff_surjective :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p),
      SurjectiveOnObjects p ↔ Surjective p)

#check
  (AlgebraicGeometry.Groupoids.Hom.SurjectiveOnObjects.of_surjective :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      (p : X ⟶ Y) [Surjective p], SurjectiveOnObjects p)

#check
  (AlgebraicGeometry.Groupoids.Hom.SurjectiveOnObjects.iff_has :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p),
      SurjectiveOnObjects p ↔ has (@AlgebraicSpace.Surjective S) p)

#check
  (AlgebraicGeometry.Groupoids.Hom.Surjective.of_surjectiveOnObjects :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p)
      [SurjectiveOnObjects p], Surjective p)
