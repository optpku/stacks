module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Schemes as algebraic spaces

A scheme `T` over `S` determines an algebraic space over `S` whose functor of points is
the representable presheaf `yoneda.obj T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- The public constructor is owned by the reusable functor-of-points module. -/
#check (AlgebraicGeometry.AlgebraicSpace.ofOver :
  ∀ {S : AlgebraicGeometry.Scheme.{u}},
    CategoryTheory.Over S → AlgebraicGeometry.AlgebraicSpace S)

end AlgebraicGeometry.AlgebraicSpace
