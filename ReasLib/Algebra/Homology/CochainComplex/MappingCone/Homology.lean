module

public import ReasLib.Algebra.Homology.CochainComplex.HomologyMap.Bounds
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of mapping cones near a bound

The mapping cone converts an isomorphism-above and epimorphism-at condition on a cochain map into
cohomology vanishing.  This bridge is independent of projective lifting applications.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CochainComplex.MappingCone.Homology

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {E L : CochainComplex A ℤ}

/-- If a cochain map is an isomorphism on cohomology above `n` and an epimorphism at `n`, then its
mapping cone has zero cohomology in every degree at least `n`. -/
@[stacks 064E "mapping-cone cohomology vanishing"]
theorem isZero_of_iso_epi (f : E ⟶ L) (n i : ℤ)
    (h_iso : HomologyMap.IsIsoAbove f n) (h_epi : HomologyMap.IsEpiAt f n)
    (hi : n ≤ i) : IsZero ((mappingCone f).homology i) := sorry

end CochainComplex.MappingCone.Homology
