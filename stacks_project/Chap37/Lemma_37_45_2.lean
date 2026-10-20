module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.DenseOpen
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.45.2: every quasi-finite morphism of schemes is finite after restriction over
some dense open subset of its target. -/
@[stacks 03I1] #check
  (AlgebraicGeometry.Scheme.Hom.exists_dense_open_isFinite_restrict_of_quasiFinite :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [AlgebraicGeometry.Scheme.Hom.QuasiFinite f],
      ∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (f ∣_ U))
