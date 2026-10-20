/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Intersection
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tor.Regular

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
  (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
  (F G : X.left.Modules) [F.IsCoherent] [G.IsCoherent]
  (r s : ℤ)

/-- If two coherent modules on a regular variety have support dimensions at most `r` and
`s`, and their common support has dimension at most `r + s - X.dimension`, then their
degree-`r` and degree-`s` associated cycles intersect properly. -/
theorem associatedCycles_intersectProperly
    (hF : ∀ x ∈ RingedSpace.moduleSupport F,
      X.hom.relativeDimensionFunction (fun _ ↦ 0) x ≤ r)
    (hG : ∀ x ∈ RingedSpace.moduleSupport G,
      X.hom.relativeDimensionFunction (fun _ ↦ 0) x ≤ s)
    (hFG : ∀ x ∈ RingedSpace.moduleSupport F ∩ RingedSpace.moduleSupport G,
      X.hom.relativeDimensionFunction (fun _ ↦ 0) x ≤
        r + s - (X.dimension : ℤ)) :
    AlgebraicCycle.IntersectProperly
      (F.associatedCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
      (G.associatedCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s) := sorry

/-- Under the support-dimension bounds for proper intersection, the intersection of two
associated cycles is the alternating sum of the associated cycles of their Tor sheaves. -/
theorem intersection_associatedCycle_eq_finsum_tor
    [RingedSpace.ModuleDerived.Tensor.Has X.left.toRingedSpace]
    (hF : ∀ x ∈ RingedSpace.moduleSupport F,
      X.hom.relativeDimensionFunction (fun _ ↦ 0) x ≤ r)
    (hG : ∀ x ∈ RingedSpace.moduleSupport G,
      X.hom.relativeDimensionFunction (fun _ ↦ 0) x ≤ s)
    (hFG : ∀ x ∈ RingedSpace.moduleSupport F ∩ RingedSpace.moduleSupport G,
      X.hom.relativeDimensionFunction (fun _ ↦ 0) x ≤
        r + s - (X.dimension : ℤ)) :
    AlgebraicCycle.intersection
        (F.associatedCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
        (G.associatedCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
        (associatedCycles_intersectProperly X F G r s hF hG hFG) =
      ∑ᶠ p : ℕ, (Int.negOnePow p : ℤ) •
        Scheme.Modules.associatedCycle (RingedSpace.ModuleDerived.tor p F G)
          (X.hom.relativeDimensionFunction (fun _ ↦ 0))
          (r + s - (X.dimension : ℤ)) := sorry

end AlgebraicGeometry.SchemeOverField
