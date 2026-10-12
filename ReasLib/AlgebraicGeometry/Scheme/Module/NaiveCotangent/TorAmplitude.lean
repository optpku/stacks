/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.AffineComparison.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.TorDimension.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.TorAmplitude
public import ReasLib.RingTheory.RingHom.Perfect.Basic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.NaiveCotangent

/-- The derived naive cotangent complex of a local complete-intersection morphism is perfect. -/
@[stacks 0FV6 "perfectness component"]
theorem isPerfect_of_lci
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    RingedSpace.ModuleDerived.IsPerfect
      (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) := sorry

/-- The derived naive cotangent complex of a local complete-intersection morphism has
Tor-amplitude in `[-1, 0]`. -/
@[stacks 0FV6 "Tor-amplitude component"]
theorem hasTorAmplitudeIn_of_lci
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    RingedSpace.HasTorAmplitudeIn
      (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) (-1) 0 := sorry

/-- The derived naive cotangent complex of a local complete-intersection morphism is perfect
and has Tor-amplitude in `[-1, 0]`. -/
theorem isPerfect_and_hasTorAmplitudeIn_of_lci
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    RingedSpace.ModuleDerived.IsPerfect
        (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) ∧
      RingedSpace.HasTorAmplitudeIn
        (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) (-1) 0 := sorry

/-- For a flat finitely presented scheme morphism, being a local complete intersection,
being syntomic, having derived naive cotangent complex of Tor-amplitude in `[-1, 0]`, and
having that complex perfect with the same Tor-amplitude are equivalent. -/
theorem flatFinitePresentation_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [Scheme.Hom.FinitePresentation f] :
    List.TFAE [LocallyOfType RingHom.IsLocalCompleteIntersection f,
      Syntomic f,
      RingedSpace.HasTorAmplitudeIn
        (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) (-1) 0,
      RingedSpace.ModuleDerived.IsPerfect
          (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) ∧
        RingedSpace.HasTorAmplitudeIn
          (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) (-1) 0] := sorry

/-- For a perfect morphism of locally Noetherian schemes, being a local complete
intersection, having derived naive cotangent complex of Tor-amplitude in `[-1, 0]`, and
having that complex perfect with the same Tor-amplitude are equivalent. -/
@[stacks 0FK2]
theorem perfect_tfae {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyOfType RingHom.IsPerfectRingMap f] :
    List.TFAE [LocallyOfType RingHom.IsLocalCompleteIntersection f,
      RingedSpace.HasTorAmplitudeIn
        (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) (-1) 0,
      RingedSpace.ModuleDerived.IsPerfect
          (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) ∧
        RingedSpace.HasTorAmplitudeIn
          (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) (-1) 0] := sorry

end AlgebraicGeometry.Scheme.Hom.NaiveCotangent
