module

public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition.Syntomic
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.17.1: The property that a scheme is locally Noetherian and satisfies Serre's
condition `(S_k)` is local in the syntomic topology.
-/
@[stacks 036A] #check
  (AlgebraicGeometry.Scheme.satisfiesSerreConditionS.syntomicLocal :
    ∀ k : ℕ,
      CategoryTheory.ObjectProperty.IsLocal
        (fun X : AlgebraicGeometry.Scheme.{u} ↦
          AlgebraicGeometry.IsLocallyNoetherian X ∧
            AlgebraicGeometry.Scheme.satisfiesSerreConditionS X k)
        AlgebraicGeometry.Scheme.bigSyntomicPrecoverage)
