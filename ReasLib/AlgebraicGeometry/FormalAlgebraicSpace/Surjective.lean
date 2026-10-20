/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction.AlgebraicSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Surjectivity of morphisms of formal algebraic spaces

Surjectivity is defined by the induced morphism between explicit reductions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.ReductionData

/-- A morphism of formal algebraic spaces is surjective when its induced morphism
between the given reductions is surjective. -/
def Surjective {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) : Prop :=
  AlgebraicSpace.Surjective (RX.map RY f)

/-- Surjectivity is equivalent to surjectivity of the induced reduction morphism. -/
theorem surjective_iff {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    Surjective RX RY f ↔ AlgebraicSpace.Surjective (RX.map RY f) :=
  Iff.rfl

/-- An isomorphism of formal algebraic spaces is surjective on their reductions. -/
theorem surjective_of_isIso {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) [IsIso f] :
    Surjective RX RY f :=
  sorry

/-- The identity morphism is surjective on a reduction. -/
theorem surjective_id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (RX : ReductionData X) :
    Surjective RX RX (𝟙 X) :=
  surjective_of_isIso RX RX (𝟙 X)

/-- For algebraic spaces with their canonical reductions, surjectivity agrees
with surjectivity as a morphism of algebraic spaces. -/
theorem surjective_functorOfPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X.functorOfPoints ⟶ Y.functorOfPoints) :
    Surjective (ofAlgebraicSpace X) (ofAlgebraicSpace Y) f ↔
      AlgebraicSpace.Surjective f :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.ReductionData
