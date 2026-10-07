module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.FlatCokernel
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.OpensRingedSite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat boundary cokernels on ringed spaces

The lower Tor-amplitude bound is the mathematical input controlling the boundary cokernel.  The
interval theorem is retained as the source-facing bridge for Lemma 20.48.2.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.FlatCokernel

variable {X : RingedSpace.{u}}

/-- A bounded-above canonically termwise-flat representative with lower Tor-amplitude bound
`a` has a flat opcycles object in degree `a`. -/
theorem ofTorAmplitudeGE
    (E : CochainComplex (Modules X) ℤ) (a : ℤ)
    (hbounded : CochainComplex.minus (Modules X) E)
    (hFlat : HomologicalComplex.IsTermwiseFlat E)
    (hTor : HasTorAmplitudeGE (DerivedCategory.Q.obj E) a) :
    IsFlat (E.opcycles a) := sorry

/-- Lemma 20.48.2: a bounded-above complex of flat `O_X`-modules whose derived object has
Tor-amplitude in `[a, b]` has flat cokernel at the differential leaving degree `a - 1`. -/
@[stacks 08CH]
theorem ofTorAmplitudeIn
    (E : CochainComplex (Modules X) ℤ) (a b : ℤ)
    (hbounded : CochainComplex.minus (Modules X) E)
    (hFlat : ∀ n : ℤ, SheafOfModules.IsFlat (E.X n))
    (hTor : HasTorAmplitudeIn (DerivedCategory.Q.obj E) a b) :
    SheafOfModules.IsFlat (cokernel (E.dFrom (a - 1))) := sorry

end AlgebraicGeometry.RingedSpace.FlatCokernel
