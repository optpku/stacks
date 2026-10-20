module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Object
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace IsDM

/-- Let `X` be an algebraic stack. Let `W` be an algebraic
space, and let `f : W.toGroupoids ⟶ X` be a surjective, flat, locally finitely
presented morphism. If `f` is unramified (i.e., étale, i.e., `X` is
Deligne-Mumford), then `X` is DM. -/
@[stacks 06MB]
theorem of_unramified {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {W : AlgebraicSpace S} (f : W.toGroupoids ⟶ X)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f]
    (h_unramified : Groupoids.Hom.has (@AlgebraicSpace.Unramified S) f) :
    IsDM X :=
  sorry

end IsDM

namespace IsQuasiDM

/-- Let `X` be an algebraic stack. Let `W` be an algebraic
space, and let `f : W.toGroupoids ⟶ X` be a surjective, flat, locally finitely
presented morphism. If `f` is locally quasi-finite, then `X` is quasi-DM. -/
@[stacks 06MB]
theorem of_locallyQuasiFinite {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {W : AlgebraicSpace S} (f : W.toGroupoids ⟶ X)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f]
    (h_locallyQuasiFinite :
      Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) f) :
    IsQuasiDM X :=
  sorry

end IsQuasiDM

end AlgebraicGeometry.AlgebraicStack
