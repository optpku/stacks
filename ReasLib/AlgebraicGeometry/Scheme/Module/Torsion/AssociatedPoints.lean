/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.EmbeddedPoints.Serre
public import ReasLib.RingTheory.Ideal.AssociatedPrime.TorsionFree

/-!
# Torsion-free scheme modules and associated points

This file characterizes nonzero coherent torsion-free modules on locally Noetherian integral
schemes through their associated points, support, embedded associated points, and Serre's
condition `(S_1)`.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

namespace IsTorsionFree

/-- A nonzero coherent module on a locally Noetherian integral scheme is torsion free exactly
when its only associated point is the generic point. -/
theorem iff_associatedPoints_eq_singleton_genericPoint (hℱ : ¬ IsZero ℱ) :
    IsTorsionFree ℱ ↔ associatedPoints ℱ = ({genericPoint X} : Set X) := sorry

end IsTorsionFree

namespace associatedPoints

/-- The generic point is the only associated point of a coherent module exactly when it lies in
the module's support and the module has no embedded associated points. -/
theorem eq_singleton_genericPoint_iff :
    associatedPoints ℱ = ({genericPoint X} : Set X) ↔
      genericPoint X ∈ moduleSupport ℱ ∧
        embeddedAssociatedPoints ℱ = (∅ : Set X) := sorry

end associatedPoints

namespace IsTorsionFree

/-- A nonzero coherent module on a locally Noetherian integral scheme is torsion free exactly
when the generic point lies in its support and it has no embedded associated points. -/
theorem iff_genericPoint_mem_support_and_embeddedAssociatedPoints_eq_empty
    (hℱ : ¬ IsZero ℱ) :
    IsTorsionFree ℱ ↔ genericPoint X ∈ moduleSupport ℱ ∧
      embeddedAssociatedPoints ℱ = (∅ : Set X) := by
  rw [iff_associatedPoints_eq_singleton_genericPoint ℱ hℱ,
    associatedPoints.eq_singleton_genericPoint_iff]

/-- A nonzero coherent module on a locally Noetherian integral scheme is torsion free exactly
when the generic point lies in its support and the module satisfies Serre's condition `(S_1)`. -/
theorem iff_genericPoint_mem_support_and_satisfiesSerreConditionS_one
    (hℱ : ¬ IsZero ℱ) :
    IsTorsionFree ℱ ↔ genericPoint X ∈ moduleSupport ℱ ∧
      satisfiesSerreConditionS ℱ 1 := by
  rw [iff_genericPoint_mem_support_and_embeddedAssociatedPoints_eq_empty ℱ hℱ,
    embeddedAssociatedPoints_eq_empty_iff_satisfiesSerreConditionS_one]

/-- For a nonzero coherent module on a locally Noetherian integral scheme, torsion-freeness,
having only the generic associated point, support together with Serre's condition `(S_1)`, and
support together with the absence of embedded associated points are equivalent. -/
theorem tfae_associatedPoints_support_serreS1 (hℱ : ¬ IsZero ℱ) :
    List.TFAE
      [ IsTorsionFree ℱ,
        associatedPoints ℱ = ({genericPoint X} : Set X),
        genericPoint X ∈ moduleSupport ℱ ∧ satisfiesSerreConditionS ℱ 1,
        genericPoint X ∈ moduleSupport ℱ ∧ embeddedAssociatedPoints ℱ = (∅ : Set X) ] := by
  tfae_have 1 ↔ 2 := iff_associatedPoints_eq_singleton_genericPoint ℱ hℱ
  tfae_have 1 ↔ 3 := iff_genericPoint_mem_support_and_satisfiesSerreConditionS_one ℱ hℱ
  tfae_have 1 ↔ 4 :=
    iff_genericPoint_mem_support_and_embeddedAssociatedPoints_eq_empty ℱ hℱ
  tfae_finish

end IsTorsionFree

end AlgebraicGeometry.Scheme.Modules
