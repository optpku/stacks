module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections

/-!
# Integral closures in global sections

This module studies the integral closure of a base field in the global
functions of a scheme over that field.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The integral closure of the base field of `f` in the bundled global-sections algebra. -/
@[stacks 04MI "base-field integral-closure subalgebra"]
noncomputable abbrev baseFieldIntegralClosureAlg {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) : Subalgebra k (globalSectionsAlg f) :=
  integralClosure k (globalSectionsAlg f)

/-- The integral closure of the base field of `f` in the global sections ring, viewed as a
subring of that global sections ring. -/
@[stacks 04MI "base-field integral-closure subring"]
noncomputable def baseFieldIntegralClosure {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) : Subring (Scheme.globalSectionsRing X) :=
  (baseFieldIntegralClosureAlg f).toSubring

/-- The base-field integral closure is the subring underlying the integral closure in the
canonical global-sections algebra. -/
theorem baseFieldIntegralClosure_def {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) :
    f.baseFieldIntegralClosure = (baseFieldIntegralClosureAlg f).toSubring := sorry

/-- For a connected reduced scheme over a field, the integral closure of the base field in
its global sections is a field. -/
@[stacks 04MI]
theorem integralClosure_isField_of_connectedReduced {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) [ConnectedSpace X] [IsReduced X] :
    IsField (integralClosure k (globalSectionsAlg f)) := sorry

/-- For a connected reduced scheme, the base-field integral closure in global sections is a
field. -/
theorem baseFieldIntegralClosure_isField {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) [ConnectedSpace X] [IsReduced X] :
    IsField f.baseFieldIntegralClosure := sorry

end AlgebraicGeometry.Scheme.Hom
