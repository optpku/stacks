module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Tactic.CrossRefAttribute

/-!
# Acyclic complexes and vanishing homology

This leaf records the shape-independent characterization of an acyclic homological complex by
the vanishing of all its homology objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {ι : Type w} {c : ComplexShape ι} (K : HomologicalComplex C c)

/-- A homological complex with homology objects in every degree is acyclic exactly when all of
those homology objects are zero. -/
@[stacks 07A1 "acyclicity characterized by vanishing homology"]
theorem acyclic_iff_forall_isZero_homology [∀ i, K.HasHomology i] :
    K.Acyclic ↔ ∀ i, IsZero (K.homology i) := sorry

end HomologicalComplex
