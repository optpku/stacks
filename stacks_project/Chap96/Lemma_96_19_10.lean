module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.CoveringLift
import StacksCheckRecall

/-!
# Covering lifts of representable surjective 1-morphisms

A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces, surjective, and either flat and locally of finite presentation
or smooth admits local lifts of every object after an fppf or étale covering.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/- Lemma 96.19.10 (1): Let `f : X ⟶ Y` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. If `f` is representable by algebraic spaces,
surjective, flat, and locally of finite presentation, then for any object `y`
of `Y` there exists an fppf covering `{y_i ⟶ y}` and objects `x_i` of `X` such
that `f(x_i) ≅ y_i` in `Y`. -/
@[stacks 06XH]
#check (AlgebraicGeometry.Groupoids.Hom.exists_fppfCovering_iso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [Surjective f] [Flat f] [LocallyOfFinitePresentation f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y),
    existsCoveringLift StandardTopology.fppf f y)

/- Lemma 96.19.10 (2): Let `f : X ⟶ Y` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. If `f` is representable by algebraic spaces,
surjective, and smooth, then for any object `y` of `Y` there exists an étale
covering `{y_i ⟶ y}` and objects `x_i` of `X` such that `f(x_i) ≅ y_i` in `Y`. -/
@[stacks 06XH]
#check (AlgebraicGeometry.Groupoids.Hom.exists_etaleCovering_iso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [Surjective f] [Smooth f] {U : Over S}
    (y : GroupoidsOver.slice U ⟶ Y),
    existsCoveringLift StandardTopology.etale f y)

end AlgebraicGeometry.Groupoids.Hom
