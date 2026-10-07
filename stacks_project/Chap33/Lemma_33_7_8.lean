module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.CompactOpen

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

/- Lemma 33.7.8: let `k` be a field, let `X` be a scheme over `k`, let `A` be a `k`-algebra, and
let `V ⊆ X_A` be a quasi-compact open. Then there exists a finitely generated `k`-subalgebra
`A' ⊆ A` and a quasi-compact open `V' ⊆ X_{A'}` whose inverse image in `X_A` is `V`. -/
@[stacks 0388] #check
  (AlgebraicGeometry.Scheme.AffineBaseChange.exists_fgSubalgebra_compactOpen_preimage_eq :
    ∀ {k A : Type u} [Field k] [CommRing A] [Algebra k A]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
      (V : CompactOpens (Scheme.AffineBaseChange.baseChange k A f).carrier),
      ∃ (A' : Subalgebra k A) (_ : A'.FG),
        ∃ V' : CompactOpens (Scheme.AffineBaseChange.baseChange k A' f).carrier,
          (Opens.map (Scheme.AffineBaseChange.Subalgebra.map f A').base).obj V'.toOpens =
            V.toOpens)
