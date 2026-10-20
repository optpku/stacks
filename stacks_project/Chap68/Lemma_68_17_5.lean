/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions.InheritedFromTarget
import StacksCheckRecall

/-!
# Object-level recovery of property (β), decent, and reasonable algebraic spaces

If `Y` has property (ω) and a morphism `f : X ⟶ Y` of algebraic spaces has relative
(ω), for `ω` among property (β), decent, and reasonable, then `X` has (ω).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.17.5 (1): If `Y` has property (β) and `f : X ⟶ Y` has property (β),
then `X` has property (β). -/
@[stacks 0ABY] #check
  (AlgebraicGeometry.AlgebraicSpace.hasPropertyBeta_inheritedFromTarget :
    ∀ {S : Scheme.{u}},
    InheritedFromTarget (@HasPropertyBeta S : ObjectProperty (AlgebraicSpace S))
      (@PropertyBeta S : MorphismProperty (AlgebraicSpace S)))

/- Lemma 68.17.5 (2): If `Y` is decent and `f : X ⟶ Y` is decent, then `X` is
decent. -/
@[stacks 0ABY] #check
  (AlgebraicGeometry.AlgebraicSpace.isDecent_inheritedFromTarget :
    ∀ {S : Scheme.{u}},
    InheritedFromTarget (@IsDecent S : ObjectProperty (AlgebraicSpace S))
      (@Decent S : MorphismProperty (AlgebraicSpace S)))

/- Lemma 68.17.5 (3): If `Y` is reasonable and `f : X ⟶ Y` is reasonable, then
`X` is reasonable. -/
@[stacks 0ABY] #check
  (AlgebraicGeometry.AlgebraicSpace.isReasonable_inheritedFromTarget :
    ∀ {S : Scheme.{u}},
    InheritedFromTarget (@IsReasonable S : ObjectProperty (AlgebraicSpace S))
      (@Reasonable S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.HasPropertyBeta.of_propertyBeta :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [HasPropertyBeta Y] → [PropertyBeta f] → HasPropertyBeta X)

#check (AlgebraicGeometry.AlgebraicSpace.IsDecent.of_decent :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [IsDecent Y] → [Decent f] → IsDecent X)

#check (AlgebraicGeometry.AlgebraicSpace.IsReasonable.of_reasonable :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [IsReasonable Y] → [Reasonable f] → IsReasonable X)
