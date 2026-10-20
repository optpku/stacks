module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.Extension
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

/- Lemma 37.48.4: a surjective finite morphism over a quasi-compact open subscheme
extends to a surjective finite morphism over the ambient scheme whose pullback is
isomorphic to the original morphism over the open subscheme. -/
@[stacks 0CNY] #check
  (AlgebraicGeometry.IsFinite.exists_surjective_extension :
    ∀ {S V : AlgebraicGeometry.Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
        (U : S.Opens) [AlgebraicGeometry.QuasiCompact U.ι] (p : V ⟶ U)
        [AlgebraicGeometry.Surjective p] [AlgebraicGeometry.IsFinite p],
      ∃ (Vbar : AlgebraicGeometry.Scheme.{u}) (q : Vbar ⟶ S),
        AlgebraicGeometry.IsFinite q ∧ AlgebraicGeometry.Surjective q ∧
          Nonempty (Over.mk (pullback.snd q U.ι) ≅ Over.mk p))
