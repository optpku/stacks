module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.FiniteNeighborhood
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 30.21.2: over a locally Noetherian target, a proper scheme morphism with finite
point-set fibre over `s` is finite after restriction to some open neighbourhood of `s`.
The checked stronger theorem omits local Noetherianity and implies this specialization;
`f ∣_ V` is the canonical restriction from the inverse-image open subscheme to `V`. -/
@[stacks 02OH] #check
  (AlgebraicGeometry.Scheme.Hom.exists_isFinite_morphismRestrict_of_finite_preimage_singleton :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.IsProper f]
      (s : S),
      Set.Finite (f ⁻¹' ({s} : Set S)) →
        ∃ V : S.Opens, s ∈ V ∧ AlgebraicGeometry.IsFinite (f ∣_ V))
