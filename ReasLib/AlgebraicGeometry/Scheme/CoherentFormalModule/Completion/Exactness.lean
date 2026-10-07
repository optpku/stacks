module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Affine
import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Restriction
import Mathlib.RingTheory.AdicCompletion.Exactness

/-!
# Exactness of coherent completion

The primary theorem concerns the canonical ideal-power quotient completion functor. A companion
theorem retains the same conclusion for any completion presentation with the specified stage
identifications.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentCompletion

/-- Lemma 30.23.4 (0881): canonical completion of coherent modules along an ideal sheaf is exact. -/
@[stacks 0881 "exactness of canonical coherent completion"]
theorem exact {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) :
    exactFunctor (RingedSpace.Coh X.toRingedSpace) (Scheme.CoherentFormalModules X I)
      (functor I) := sorry

/-- Canonical coherent completion preserves finite limits. -/
@[stacks 0881 "finite-limit preservation by canonical completion"]
instance preservesFiniteLimits {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) :
    PreservesFiniteLimits (functor I) := sorry

/-- Canonical coherent completion preserves finite colimits. -/
@[stacks 0881 "finite-colimit preservation by canonical completion"]
instance preservesFiniteColimits {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) :
    PreservesFiniteColimits (functor I) := sorry

/-- Canonical coherent completion is additive. -/
@[stacks 0881 "additivity of canonical completion"]
instance additive {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) :
    (functor I).Additive := sorry

end AlgebraicGeometry.Scheme.CoherentCompletion

/-- Any completion presentation with the canonical ideal-power quotient stages is exact. -/
@[stacks 0881 "exactness of a coherent completion presentation"]
theorem coherentCompletionFunctor_exact
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I) :
    exactFunctor (RingedSpace.Coh X.toRingedSpace) (Scheme.CoherentFormalModules X I)
      ctx.toFunctor := sorry
