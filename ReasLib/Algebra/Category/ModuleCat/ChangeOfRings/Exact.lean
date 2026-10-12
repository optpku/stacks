/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness under change of rings

This file packages the exactness properties of restriction and extension of scalars as theorem
values.  The restriction theorem is stated for arbitrary rings and independent universe levels;
the extension criteria use the canonical tensor functor for commutative rings.
-/

@[expose] public section

open CategoryTheory Limits

universe v u u₁ u₂

namespace ModuleCat

section Restriction

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]

/-- Restriction of scalars does not change the underlying functions in a short complex. -/
private theorem restrictScalars_map_exact_of_ring (f : R →+* S)
    (T : ShortComplex (ModuleCat.{v} S)) (hT : T.Exact) :
    (T.map (restrictScalars.{v} f)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢
  exact hT

/-- Restriction of scalars along a ring homomorphism is exact. -/
@[stacks 03B8]
theorem restrictScalars_exact (f : R →+* S) :
    exactFunctor (ModuleCat.{v} S) (ModuleCat.{v} R) (restrictScalars.{v} f) := by
  exact ((Functor.exact_tfae (restrictScalars.{v} f)).out 1 3).mp
    (restrictScalars_map_exact_of_ring f)

/-- Restriction of scalars along a homomorphism of arbitrary rings preserves finite limits. -/
@[stacks 03B8 "restriction preserves finite limits"]
instance (priority := 1100) restrictScalars_preservesFiniteLimits (f : R →+* S) :
    PreservesFiniteLimits (restrictScalars.{v} f) :=
  (restrictScalars_exact f).1

/-- Restriction of scalars along a homomorphism of arbitrary rings preserves finite colimits. -/
@[stacks 03B8 "restriction preserves finite colimits"]
instance (priority := 1100) restrictScalars_preservesFiniteColimits (f : R →+* S) :
    PreservesFiniteColimits (restrictScalars.{v} f) :=
  (restrictScalars_exact f).2

namespace RestrictScalars

/-- Restriction of scalars, bundled as an exact functor. -/
@[stacks 03B8 "restriction of scalars as an exact functor"]
noncomputable def exact (f : R →+* S) :
    ModuleCat.{v} S ⥤ₑ ModuleCat.{v} R :=
  ⟨ModuleCat.restrictScalars.{v} f, ModuleCat.restrictScalars_exact f⟩

end RestrictScalars

end Restriction

section Extension

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Extension of scalars is right exact, as it is the canonical left adjoint to restriction of
scalars. -/
@[stacks 03B8]
theorem extendScalars_rightExact (f : R →+* S) :
    rightExactFunctor (ModuleCat.{u} R) (ModuleCat.{u} S)
      (extendScalars.{u, u, u} f) := by
  change PreservesFiniteColimits (extendScalars.{u, u, u} f)
  infer_instance

/-- Exact extension of scalars forces the target to be flat over the source. -/
private theorem flat_of_extendScalars_exact (f : R →+* S)
    (h : exactFunctor (ModuleCat.{u} R) (ModuleCat.{u} S)
      (extendScalars.{u, u, u} f)) : f.Flat := by
  algebraize [f]
  change Module.Flat R S
  -- Local instance justification (proof-local temporary data): exactness supplies preservation of limits.
  letI : PreservesFiniteLimits (extendScalars.{u, u, u} f) := h.1
  -- Local instance justification (defeq pin): fix the universe-specific restriction functor used below.
  letI : PreservesFiniteLimits (restrictScalars.{u, u, u} f) :=
    restrictScalars_preservesFiniteLimits f
  have hComp : PreservesFiniteLimits
      (extendScalars.{u, u, u} f ⋙ restrictScalars.{u, u, u} f) :=
    comp_preservesFiniteLimits _ _
  change PreservesFiniteLimits
    (MonoidalCategory.tensorLeft (ModuleCat.of R S)) at hComp
  exact (Module.Flat.iff_preservesFiniteLimits_tensorLeft (ModuleCat.of R S)).mpr hComp

/-- Extension of scalars along a commutative ring map is exact exactly when the map is flat. -/
@[stacks 03B8]
theorem extendScalars_exact_iff_flat (f : R →+* S) :
    exactFunctor (ModuleCat.{u} R) (ModuleCat.{u} S)
        (extendScalars.{u, u, u} f) ↔
      f.Flat := by
  constructor
  · exact flat_of_extendScalars_exact f
  · intro hf
    change PreservesFiniteLimits (extendScalars.{u, u, u} f) ∧
      PreservesFiniteColimits (extendScalars.{u, u, u} f)
    exact ⟨preservesFiniteLimits_extendScalars_of_flat hf, by infer_instance⟩

/-- A flat commutative ring map has exact extension of scalars. -/
theorem extendScalars_exact_of_flat (f : R →+* S) (h_flat : f.Flat) :
    exactFunctor (ModuleCat.{u} R) (ModuleCat.{u} S)
      (extendScalars.{u, u, u} f) :=
  (extendScalars_exact_iff_flat f).mpr h_flat

namespace ExtendScalars

/-- Extension of scalars along a flat ring homomorphism, bundled as an exact
functor. -/
@[stacks 03B8 "flat extension of scalars as an exact functor"]
noncomputable def exact (f : R →+* S) (h_flat : f.Flat) :
    ModuleCat.{u} R ⥤ₑ ModuleCat.{u} S :=
  ⟨ModuleCat.extendScalars.{u, u, u} f,
    ModuleCat.extendScalars_exact_of_flat f h_flat⟩

/-- If extension of scalars is also a right adjoint, then the ring map is
flat. -/
@[stacks 04BI]
theorem flat_of_isRightAdjoint
    (f : R →+* S) [(extendScalars.{u, u, u} f).IsRightAdjoint] :
    f.Flat := by
  apply (ModuleCat.extendScalars_exact_iff_flat f).mp
  change PreservesFiniteLimits (extendScalars.{u, u, u} f) ∧
    PreservesFiniteColimits (extendScalars.{u, u, u} f)
  exact ⟨by infer_instance, by infer_instance⟩

end ExtendScalars

end Extension

end ModuleCat

-- These two established names are used unqualified by existing change-of-rings consumers.
export ModuleCat (extendScalars_exact_of_flat restrictScalars_exact)

