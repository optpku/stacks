module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Setoids
import StacksCheckRecall

/-!
# Categories fibred in groupoids representable by algebraic spaces

A category fibred in groupoids over `(Sch/S)_fppf` is representable by an algebraic
space exactly when it is fibred in setoids and its presheaf of fiberwise isomorphism
classes is an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 94.8.2: let `S` be a scheme contained in `Sch_fppf`. Let
`p : X ⟶ (Sch/S)_fppf` be a category fibred in groupoids. Then `X` is
representable by an algebraic space over `S` if and only if `X` is fibred in
setoids and the presheaf `U ↦ Ob(X_U)/≅`, identified with
`Functor.fiberIsoClassPresheaf X.p`, is an algebraic space. -/
@[stacks 02ZX]
#check (AlgebraicGeometry.IsRepresentableByAlgebraicSpace.iff_inSetoids_and_fiberClasses :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    IsRepresentableByAlgebraicSpace X ↔
      Functor.IsFibered.InSetoids X.p ∧
        ∃ F : AlgebraicSpace S,
          Nonempty
            (Functor.fiberIsoClassPresheaf X.p ≅
              F.functorOfPoints ⋙ uliftFunctor.{u + 1, u}))

/- A category fibred in groupoids representable by an algebraic space is fibred in
setoids. -/
#check (AlgebraicGeometry.IsRepresentableByAlgebraicSpace.inSetoids :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (hX : IsRepresentableByAlgebraicSpace X),
    Functor.IsFibered.InSetoids X.p)

/- The fiberwise-isomorphism-class presheaf of a category fibred in groupoids
representable by an algebraic space is naturally isomorphic, after universe lift, to
the functor of points of some algebraic space. -/
#check (AlgebraicGeometry.IsRepresentableByAlgebraicSpace.fiberClasses :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (hX : IsRepresentableByAlgebraicSpace X),
    ∃ F : AlgebraicSpace S,
      Nonempty
        (Functor.fiberIsoClassPresheaf X.p ≅
          F.functorOfPoints ⋙ uliftFunctor.{u + 1, u}))

/- A category fibred in groupoids is representable by an algebraic space once it is
fibred in setoids and its fiberwise-isomorphism-class presheaf matches an algebraic
space after universe lift. -/
#check (AlgebraicGeometry.IsRepresentableByAlgebraicSpace.of_inSetoids_of_fiberClasses :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (hSetoids : Functor.IsFibered.InSetoids X.p)
    (hClasses :
      ∃ F : AlgebraicSpace S,
        Nonempty
          (Functor.fiberIsoClassPresheaf X.p ≅
            F.functorOfPoints ⋙ uliftFunctor.{u + 1, u})),
    IsRepresentableByAlgebraicSpace X)

end AlgebraicGeometry
