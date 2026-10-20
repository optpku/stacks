module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothGroupoid.Quotient
import StacksCheckRecall

/-!
# Smooth groupoids in functors need not have smooth quotients

A smooth groupoid in functors `(U, R, s, t, c)` on `ArtinianLocalAlgCat Λ k` need
not have `[U/R]` smooth as a category cofibered in groupoids. Smoothness of the
groupoid is instead equivalent to smoothness of the quotient morphism
`U ⟶ [U/R]`.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/- Remark 90.23.2 (1): if `(U, R, s, t, c)` is a smooth groupoid in functors on
`ArtinianLocalAlgCat Λ k`, then the quotient `[U/R]` need not be a smooth
category cofibered in groupoids in the sense of Definition 90.9.1. -/
@[stacks 06KJ]
#check (CategoryTheory.GroupoidInFunctors.not_forall_isSmooth_quotient :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k],
      ¬ ∀ (G : GroupoidInFunctors.{u + 1, u, max u v} (ArtinianLocalAlgCat Λ k)),
        IsSmooth G.s G.t → Functor.IsSmooth G.quotient.p)

/- Remark 90.23.2 (2): smoothness of `(U, R, s, t, c)` is equivalent to smoothness
of the quotient morphism `U ⟶ [U/R]`. -/
@[stacks 06KJ]
#check (CategoryTheory.GroupoidInFunctors.isSmooth_iff_quotientMorphism :
    ∀ G : GroupoidInFunctors.{u + 1, u, v} (ArtinianLocalAlgCat Λ k),
      IsSmooth G.s G.t ↔ BasedFunctor.IsSmooth (quotientMorphism G))

end CategoryTheory.GroupoidInFunctors
