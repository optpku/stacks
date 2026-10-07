module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Subcanonical topologies and universal effective epimorphic sieves

This module exposes the covering-sieve formulation of subcanonicity alongside
Mathlib's `GrothendieckTopology.Subcanonical` owner.  The sieve formulation
does not require chosen categorical pullbacks: base change is represented by
`Sieve.pullback`, and effective epimorphy is checked on that sieve.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Sieve

/-- A sieve is universally effective epimorphic when every pullback sieve is effective epimorphic. -/
def IsUniversallyEffectiveEpimorphic {X : C} (S : Sieve X) : Prop :=
  ∀ {Y : C} (f : Y ⟶ X), (S.pullback f).EffectiveEpimorphic

end Sieve

namespace GrothendieckTopology

/-- Definition 7.12.2 (00WQ): a topology is subcanonical exactly when every covering sieve is
universally effective epimorphic, i.e. every base change of the covering sieve is effective
epimorphic. -/
@[stacks 00WQ]
theorem subcanonical_iff_forall_cover_isUniversallyEffectiveEpimorphic
    (J : GrothendieckTopology C) :
    J.Subcanonical ↔
      ∀ {X : C} (S : Sieve X), S ∈ J X → S.IsUniversallyEffectiveEpimorphic := sorry

end GrothendieckTopology

end CategoryTheory
