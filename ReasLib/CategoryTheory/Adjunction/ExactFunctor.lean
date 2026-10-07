module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.Functor.Exactness.Additive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact functors from adjunctions

An adjunction automatically supplies colimit preservation for its left adjoint
and limit preservation for its right adjoint.  Thus preserving the complementary
finite shapes canonically bundles either adjoint as an exact functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v v' u u'

namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable {L : C ⥤ D} {R : D ⥤ C}

/-- A left adjoint preserving finite limits, bundled as an exact functor. -/
@[stacks 0038 "exact left adjoint"]
noncomputable abbrev exactLeftAdjoint (adj : L ⊣ R) [PreservesFiniteLimits L] :
    C ⥤ₑ D :=
  -- Local instance justification (proof-local temporary data): the explicit adjunction
  -- canonically supplies colimit preservation for its left adjoint.
  letI := adj.leftAdjoint_preservesColimits
  ExactFunctor.of L

/-- A right adjoint preserving finite colimits, bundled as an exact functor. -/
@[stacks 0038 "exact right adjoint"]
noncomputable abbrev exactRightAdjoint (adj : L ⊣ R) [PreservesFiniteColimits R] :
    D ⥤ₑ C :=
  -- Local instance justification (proof-local temporary data): the explicit adjunction
  -- canonically supplies limit preservation for its right adjoint.
  letI := adj.rightAdjoint_preservesLimits
  ExactFunctor.of R

end CategoryTheory.Adjunction
