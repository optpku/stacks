module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.FiniteGeneration

/-!
# Associated and weakly associated points under finite generation

Finite generation of the maximal ideal at a stalk identifies associated and weakly associated
points. On locally Noetherian schemes this gives equality of the two loci.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- If the maximal ideal of the stalk at `x` is finitely generated, then `x` is associated to a
quasicoherent module exactly when it is weakly associated to that module. -/
theorem mem_associatedPoints_iff_mem_weakAss_of_stalk_maximalIdeal_fg
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (x : X)
    (hfg : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).FG) :
    x ∈ associatedPoints ℱ ↔ x ∈ weakAss ℱ := by
  rw [mem_associatedPoints_iff, mem_associatedPrimesOfModule_iff, mem_weakAss_iff]
  exact
    Ideal.IsAssociatedToModule.iff_isWeaklyAssociatedToModule_of_fg
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) hfg

/-- On a locally Noetherian scheme, the associated and weakly associated points of a
quasicoherent module coincide. -/
theorem associatedPoints_eq_weakAss_of_isLocallyNoetherian
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [IsLocallyNoetherian X] :
    associatedPoints ℱ = weakAss ℱ := by
  ext x
  exact
    mem_associatedPoints_iff_mem_weakAss_of_stalk_maximalIdeal_fg ℱ x
      (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal (X.presheaf.stalk x)))

end AlgebraicGeometry.Scheme.Modules
