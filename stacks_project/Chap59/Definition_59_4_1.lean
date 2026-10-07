module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Covering
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 59.4.1: An indexed family is an étale covering exactly when its
images jointly cover the target and each morphism is étale. -/
@[stacks 03N5] #check (AlgebraicGeometry.Scheme.ofArrows_mem_etalePrecoverage_iff :
  ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
    {X : ι → AlgebraicGeometry.Scheme.{u}} (f : ∀ i, X i ⟶ T),
      CategoryTheory.Presieve.ofArrows X f ∈
          AlgebraicGeometry.Scheme.etalePrecoverage T ↔
        ((∀ x : T, ∃ i, x ∈ Set.range (f i)) ∧
          ∀ i, AlgebraicGeometry.Etale (f i)))
