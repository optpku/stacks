module

public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.Fibered
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 92.27.1: for a ring `Λ` and a scheme `X` over `Spec Λ`, the category
of diagrams `U ⟶ A`, with `U` open in `X` and `A` polynomial affine over
`Spec Λ`, is fibered over `X.smallZariskiSite`. Restriction by composition
gives strongly cartesian comparison morphisms. -/
@[stacks 08VJ] #check
  (AlgebraicGeometry.Scheme.CotangentSite.forgetZariski_isFibered :
    ∀ (Λ : CommRingCat.{u}) (X : AlgebraicGeometry.Scheme.{u})
      [X.Over (AlgebraicGeometry.Spec Λ)],
      (AlgebraicGeometry.Scheme.CotangentSite.forgetZariski Λ X).IsFibered)
