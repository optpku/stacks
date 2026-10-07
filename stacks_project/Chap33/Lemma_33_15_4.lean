module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Proper

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 33.15.4: let `f : X ⟶ Spec (CommRingCat.of k)` exhibit `X` as a scheme over the field `k`, and let
`K / k` be a field extension. If the base change
`XK = X ×[Spec (CommRingCat.of k)] Spec (CommRingCat.of K)` is proper over
`Spec (CommRingCat.of K)`, then `X` is proper over `Spec (CommRingCat.of k)`. -/
@[stacks 0BDF] #check
  (AlgebraicGeometry.IsProper.of_baseChangeToFieldExtension :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
      [IsProper (FieldExtension.toBase k K f)], IsProper f)
