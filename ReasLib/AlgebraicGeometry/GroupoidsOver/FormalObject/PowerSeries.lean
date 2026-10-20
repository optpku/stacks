module

public import ReasLib.AlgebraicGeometry.CompleteLocalAlgebra.PowerSeries
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Approximation

/-! # Fixed-base restriction over a power-series spectrum -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.HomStack

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.FormalObject

/-- Formal objects whose complete local base is the identity power-series algebra. -/
def overPowerSeries (k : Type u) [Field k] (𝒳 : GroupoidsOver (specPowerSeries k)) :
    ObjectProperty (FormalObject 𝒳) :=
  fun ξ ↦ ξ.base = CompleteLocalSAlgebra.powerSeries k

/-- Membership in the fixed power-series base means equality of the stored base
with the identity power-series algebra. -/
theorem overPowerSeries_iff {k : Type u} [Field k]
    {𝒳 : GroupoidsOver (specPowerSeries k)} (ξ : FormalObject 𝒳) :
    overPowerSeries k 𝒳 ξ ↔ ξ.base = CompleteLocalSAlgebra.powerSeries k := Iff.rfl

/-- Restriction of the identity fibre arrow is the identity of the restricted
formal object. -/
theorem powerSeriesRestriction_map_id {k : Type u} [Field k]
    (𝒳 : GroupoidsOver (specPowerSeries k))
    (ξ : 𝒳.p.Fiber (Over.mk (𝟙 (specPowerSeries k)))) :
    (GroupoidsOver.approximation (S := Spec (CommRingCat.of (PowerSeries k))) 𝒳).map
        (CompleteLocalObject.Hom.ofFiber (S := Spec (CommRingCat.of (PowerSeries k)))
          (CompleteLocalSAlgebra.powerSeries k) (𝟙 ξ)) =
      𝟙 (restriction (S := Spec (CommRingCat.of (PowerSeries k)))
        (CompleteLocalObject.ofFiber (CompleteLocalSAlgebra.powerSeries k) ξ)) :=
  sorry

/-- Restriction of fibre arrows over the power-series spectrum preserves composition. -/
theorem powerSeriesRestriction_map_comp {k : Type u} [Field k]
    (𝒳 : GroupoidsOver (specPowerSeries k))
    {ξ η ζ : 𝒳.p.Fiber (Over.mk (𝟙 (specPowerSeries k)))} (f : ξ ⟶ η) (g : η ⟶ ζ) :
    (GroupoidsOver.approximation (S := Spec (CommRingCat.of (PowerSeries k))) 𝒳).map
        (CompleteLocalObject.Hom.ofFiber (S := Spec (CommRingCat.of (PowerSeries k)))
          (CompleteLocalSAlgebra.powerSeries k) (f ≫ g)) =
      (GroupoidsOver.approximation (S := Spec (CommRingCat.of (PowerSeries k))) 𝒳).map
          (CompleteLocalObject.Hom.ofFiber (S := Spec (CommRingCat.of (PowerSeries k)))
          (CompleteLocalSAlgebra.powerSeries k) f) ≫
        (GroupoidsOver.approximation (S := Spec (CommRingCat.of (PowerSeries k))) 𝒳).map
          (CompleteLocalObject.Hom.ofFiber (S := Spec (CommRingCat.of (PowerSeries k)))
          (CompleteLocalSAlgebra.powerSeries k) g) := sorry

/-- The canonical restriction from the fibre over the power-series spectrum to
compatible formal objects over its positive maximal-adic truncations. -/
def powerSeriesRestriction {k : Type u} [Field k]
    (𝒳 : GroupoidsOver (specPowerSeries k)) :
    𝒳.p.Fiber (Over.mk (𝟙 (specPowerSeries k))) ⥤
      (overPowerSeries k 𝒳).FullSubcategory :=
  (overPowerSeries k 𝒳).lift
    { obj ξ := restriction (S := Spec (CommRingCat.of (PowerSeries k)))
        (CompleteLocalObject.ofFiber (CompleteLocalSAlgebra.powerSeries k) ξ)
      map f := (GroupoidsOver.approximation (S := Spec (CommRingCat.of (PowerSeries k))) 𝒳).map
        (CompleteLocalObject.Hom.ofFiber (S := Spec (CommRingCat.of (PowerSeries k)))
          (CompleteLocalSAlgebra.powerSeries k) f)
      map_id := powerSeriesRestriction_map_id 𝒳
      map_comp := powerSeriesRestriction_map_comp 𝒳 }
    (fun _ ↦ rfl)

/-- The formal object underlying restriction is the cartesian truncation system
of the complete local object associated to the fibre object. -/
theorem powerSeriesRestriction_obj {k : Type u} [Field k]
    (𝒳 : GroupoidsOver (specPowerSeries k))
    (ξ : 𝒳.p.Fiber (Over.mk (𝟙 (specPowerSeries k)))) :
    ((powerSeriesRestriction 𝒳).obj ξ).obj =
      restriction (S := Spec (CommRingCat.of (PowerSeries k)))
        (CompleteLocalObject.ofFiber (CompleteLocalSAlgebra.powerSeries k) ξ) := rfl

/-- The base of a restricted fibre object is the identity power-series algebra. -/
theorem powerSeriesRestriction_obj_base {k : Type u} [Field k]
    (𝒳 : GroupoidsOver (specPowerSeries k))
    (ξ : 𝒳.p.Fiber (Over.mk (𝟙 (specPowerSeries k)))) :
    ((powerSeriesRestriction 𝒳).obj ξ).obj.base = CompleteLocalSAlgebra.powerSeries k := rfl

end AlgebraicGeometry.GroupoidsOver.FormalObject
