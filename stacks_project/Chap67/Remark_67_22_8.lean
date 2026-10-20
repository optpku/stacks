module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocalAt.Near
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Remark 67.22.8: apply Lemma 67.22.7 to all nine nonflat cases listed in
Descent, Remark 35.32.7, by defining a morphism `f` of algebraic spaces to have
property `P` at a point `x` when `etaleLocalNear P f x` holds, i.e. when `f` has
`etaleLocal P` on some open neighbourhood of `x`. This convention does not
identify neighbourhood-flatness with flatness at a point. -/
@[stacks 04RG] #check (AlgebraicGeometry.AlgebraicSpace.etaleLocalNear :
  ∀ {S : Scheme.{u}} (P : MorphismProperty Scheme.{u}) {X Y : AlgebraicSpace S},
    (X ⟶ Y) → AlgebraicGeometry.AlgebraicSpace.Points X → Prop)
