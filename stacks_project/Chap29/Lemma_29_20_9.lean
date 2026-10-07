module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.20.9: the formal form separates the three independent components
`QuasiCompact f`, `LocallyOfFiniteType f`, and `LocallyQuasiFinite f`, because mathlib's latter
predicate does not itself impose local finite type. -/
@[stacks 01TJ] #check
  (AlgebraicGeometry.Scheme.Hom.quasiFinite_iff_quasiCompact_locallyOfFiniteType_and_locallyQuasiFinite :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.Scheme.Hom.QuasiFinite f ↔
        AlgebraicGeometry.QuasiCompact f ∧ AlgebraicGeometry.LocallyOfFiniteType f ∧
          AlgebraicGeometry.LocallyQuasiFinite f)
