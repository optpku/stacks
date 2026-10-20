module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField

/-!
# Radicial morphisms of schemes

This module defines radicial morphisms using residue-field extensions and
relates them to universally injective morphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A scheme morphism is radicial if it is injective on points and its induced residue-field
maps are purely inseparable. -/
class Radicial (f : X ⟶ S) : Prop where
  /-- The underlying map on points is injective. -/
  toInjective : Function.Injective f
  /-- Every induced map of residue fields is purely inseparable. -/
  residueField_isPurelyInseparable (x : X) :
    (f.residueFieldMap x).hom.IsPurelyInseparable

/-- A radicial scheme morphism is injective on underlying points. -/
theorem Radicial.injective [h : Radicial f] : Function.Injective f := sorry

/-- A radicial scheme morphism induces a purely inseparable extension on each residue field. -/
theorem residueField_isPurelyInseparable (x : X) [h : Radicial f] :
    IsPurelyInseparable (S.residueField (f x)) (X.residueField x) := sorry

/-- A scheme morphism is radicial exactly when it is injective on points and every induced
map of residue fields is purely inseparable. -/
theorem radicial_iff :
    Radicial f ↔ Function.Injective f ∧
      ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable := sorry

/-- A scheme morphism is radicial exactly when it is universally injective. -/
theorem radicial_iff_universallyInjective : Radicial f ↔ UniversallyInjective f := sorry

/-- A radicial scheme morphism is universally injective. -/
instance instUniversallyInjectiveOfRadicial [Radicial f] : UniversallyInjective f := sorry

/-- A universally injective scheme morphism is radicial. -/
instance radicial_of_universallyInjective [UniversallyInjective f] : Radicial f := sorry

end

end AlgebraicGeometry
