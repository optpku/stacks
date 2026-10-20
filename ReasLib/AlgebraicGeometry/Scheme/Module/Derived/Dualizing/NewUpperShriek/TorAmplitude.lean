/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek.FiberDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.RingedSpace.ModuleDerived

universe u

namespace AlgebraicGeometry.Scheme.NewUpperShriekAssignment

variable {S : Scheme.{u}} [IsNoetherian S]
variable [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
variable {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
variable {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}

/-- For a flat morphism, nontrivial cohomology of the new-upper-shriek dualizing
object at a point occurs only between the negative local fibre dimension and zero. -/
theorem cohomologyStalk_degree_mem_of_flat
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y) [Flat f.hom.left]
    (x : X.obj.left) (d : ℕ)
    (h_dimension : fiberDimensionAt f.hom.left x = (d : WithBot ℕ∞)) (i : ℤ)
    (hi : Nontrivial (cohomologyStalk (D.dualizingObject f) i x)) :
    i ∈ Set.Icc (-(d : ℤ)) 0 := sorry

/-- If a flat morphism has relative dimension at most `d`, its new-upper-shriek
dualizing object has Tor-amplitude in `[-d, 0]` over the target. -/
theorem dualizingObject_hasTorAmplitudeInOver_of_flat
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y) [Flat f.hom.left]
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules (RingedSpace.Hom.inverseImageBase f.hom.left.toShHom))]
    (d : ℕ) [Scheme.Hom.RelativeDimensionLE f.hom.left d] :
    HasTorAmplitudeInOver (f.hom.left).toShHom (D.dualizingObject f) (-(d : ℤ)) 0 := sorry

end AlgebraicGeometry.Scheme.NewUpperShriekAssignment
