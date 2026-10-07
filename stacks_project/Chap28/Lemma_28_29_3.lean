module

public import ReasLib.AlgebraicGeometry.Scheme.DenseOpen.Separated
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 28.29.3: A quasi-compact scheme admits a dense open subscheme that is separated. -/
@[stacks 03J1] #check (AlgebraicGeometry.Scheme.exists_dense_open_isSeparated :
  ∀ {X : Scheme.{u}}, [CompactSpace X] →
    ∃ U : X.Opens, U.toScheme.IsSeparated ∧ Dense (U : Set X))
