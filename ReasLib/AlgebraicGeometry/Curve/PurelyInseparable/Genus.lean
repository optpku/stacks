module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Curve.Nonconstant
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom
open Scheme.Hom.IsNonconstant

universe u

namespace AlgebraicGeometry.Curve

/-- The target of a nonconstant purely inseparable morphism of proper regular curves over a
field of positive characteristic is smooth when the source is smooth and its canonical
global-sections map is bijective. -/
theorem smooth_of_isPurelyInseparable
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (X Y : SchemeOverField k) [Curve X] [Curve Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left]
    [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom]
    (f : X ⟶ Y) (hf : f.left.IsNonconstant)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_pi : (f.left.functionFieldMap
      ((AlgebraicGeometry.isDominant_iff_map_genericPoint_eq f.left).mp
        (isDominant_of_curves hf))).IsPurelyInseparable) :
    Smooth Y.hom := sorry

/-- The canonical global-sections map of the target of a nonconstant purely inseparable
morphism of proper regular curves over a field of positive characteristic is bijective
when the source is smooth and its canonical global-sections map is bijective. -/
theorem globalSectionsMap_bijective_of_isPurelyInseparable
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (X Y : SchemeOverField k) [Curve X] [Curve Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left]
    [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom]
    (f : X ⟶ Y) (hf : f.left.IsNonconstant)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_pi : (f.left.functionFieldMap
      ((AlgebraicGeometry.isDominant_iff_map_genericPoint_eq f.left).mp
        (isDominant_of_curves hf))).IsPurelyInseparable) :
    Function.Bijective (Scheme.Hom.globalSectionsMap Y.hom) := sorry

/-- A nonconstant purely inseparable morphism of proper regular curves over a field of
positive characteristic preserves genus when the source is smooth and its canonical
global-sections map is bijective. -/
theorem genus_eq_of_isPurelyInseparable
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (X Y : SchemeOverField k) [Curve X] [Curve Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left]
    [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom]
    (f : X ⟶ Y) (hf : f.left.IsNonconstant)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_pi : (f.left.functionFieldMap
      ((AlgebraicGeometry.isDominant_iff_map_genericPoint_eq f.left).mp
        (isDominant_of_curves hf))).IsPurelyInseparable) :
    SchemeOverField.genus Y (AlgebraicGeometry.topologicalKrullDim_eq_one Y)
        (globalSectionsMap_bijective_of_isPurelyInseparable p X Y f hf hΓ h_pi) =
      SchemeOverField.genus X (AlgebraicGeometry.topologicalKrullDim_eq_one X) hΓ := sorry

end AlgebraicGeometry.Curve
