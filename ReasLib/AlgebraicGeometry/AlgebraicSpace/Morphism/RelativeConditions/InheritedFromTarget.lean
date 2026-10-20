/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions
public import Mathlib.CategoryTheory.ObjectProperty.InheritedFromHom

/-!
# Inheritance of algebraic-space conditions from the target

Property (β), decency, and reasonableness pass from the target of a morphism to
its source when the morphism satisfies the corresponding relative condition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Property (β) is inherited from the target along morphisms with property (β). -/
instance hasPropertyBeta_inheritedFromTarget {S : Scheme.{u}} :
    InheritedFromTarget (@HasPropertyBeta S : ObjectProperty (AlgebraicSpace S))
      (@PropertyBeta S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- Decency is inherited from the target along decent morphisms. -/
instance isDecent_inheritedFromTarget {S : Scheme.{u}} :
    InheritedFromTarget (@IsDecent S : ObjectProperty (AlgebraicSpace S))
      (@Decent S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- Reasonableness is inherited from the target along reasonable morphisms. -/
instance isReasonable_inheritedFromTarget {S : Scheme.{u}} :
    InheritedFromTarget (@IsReasonable S : ObjectProperty (AlgebraicSpace S))
      (@Reasonable S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- If `Y` has property (β) and `f : X ⟶ Y` has property (β), then `X` has
property (β). -/
theorem HasPropertyBeta.of_propertyBeta {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [HasPropertyBeta Y] [PropertyBeta f] : HasPropertyBeta X :=
  InheritedFromTarget.of_hom_of_target f
    (inferInstance : PropertyBeta f) inferInstance

/-- If `Y` is decent and `f : X ⟶ Y` is decent, then `X` is decent. -/
theorem IsDecent.of_decent {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsDecent Y] [Decent f] : IsDecent X :=
  InheritedFromTarget.of_hom_of_target f
    (inferInstance : Decent f) inferInstance

/-- If `Y` is reasonable and `f : X ⟶ Y` is reasonable, then `X` is reasonable. -/
theorem IsReasonable.of_reasonable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsReasonable Y] [Reasonable f] : IsReasonable X :=
  InheritedFromTarget.of_hom_of_target f
    (inferInstance : Reasonable f) inferInstance

end AlgebraicGeometry.AlgebraicSpace
