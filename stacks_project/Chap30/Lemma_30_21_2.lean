module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite restrictions of proper morphisms over locally Noetherian bases

Over a locally Noetherian target, a proper morphism of schemes with a finite point-set fibre
becomes finite after restriction to some open neighbourhood of that point.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.IsFinite

/-- Lemma 30.21.2: let `f : X ⟶ S` be a morphism of schemes, and let `s ∈ S`. Assume
`S` is locally Noetherian, `f` is proper, and `f ⁻¹' {s}` is a finite set. Then there
exists an open neighbourhood `V ⊂ S` of `s` such that `f ∣_ V : f ⁻¹ᵁ V ⟶ V` is finite.
(A more general version is Lemma 37.44.2.) -/
@[stacks 02OH]
theorem exists_morphismRestrict_of_finite_preimage_singleton {X S : Scheme.{u}}
    [IsLocallyNoetherian S] (f : X ⟶ S) [IsProper f] (s : S)
    (hs : Set.Finite (f ⁻¹' ({s} : Set S))) :
    ∃ V : S.Opens, s ∈ V ∧ IsFinite (f ∣_ V) := sorry

end AlgebraicGeometry.IsFinite
