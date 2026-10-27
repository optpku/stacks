/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction.AlgebraicSpace
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction.Class
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
import Mathlib.Tactic.CrossRefAttribute

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

/-- The composition of two morphisms that are surjective on the given reductions
is surjective on those reductions. -/
theorem surjective_comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    (RX : ReductionData X) (RY : ReductionData Y) (RZ : ReductionData Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Surjective RX RY f → Surjective RY RZ g → Surjective RX RZ (f ≫ g) :=
  sorry

/-- For algebraic spaces with their canonical reductions, surjectivity agrees
with surjectivity as a morphism of algebraic spaces. -/
theorem surjective_functorOfPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X.functorOfPoints ⟶ Y.functorOfPoints) :
    Surjective (ofAlgebraicSpace X) (ofAlgebraicSpace Y) f ↔
      AlgebraicSpace.Surjective f :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.ReductionData

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The induced morphism of algebraic-space reductions along a morphism of
formal algebraic spaces, as the unique factor of `reductionι X ≫ f` through
`reductionι Y`. -/
def mapReduction {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [RX : Reduction X] [RY : Reduction Y] (f : X ⟶ Y) :
    reduction X ⟶ reduction Y :=
  ReductionData.map RX.toReductionData RY.toReductionData f

/-- `mapReduction f` factors `reductionι X ≫ f` through `reductionι Y`. -/
theorem mapReduction_spec {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [RX : Reduction X] [RY : Reduction Y] (f : X ⟶ Y) :
    NatTrans.vcomp (mapReduction f) (reductionι Y) =
      NatTrans.vcomp (reductionι X) f :=
  ReductionData.map_spec RX.toReductionData RY.toReductionData f

/-- A morphism of reductions over `f` equals `mapReduction f`. -/
theorem mapReduction_unique {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [RX : Reduction X] [RY : Reduction Y] (f : X ⟶ Y) {g : reduction X ⟶ reduction Y}
    (hg : NatTrans.vcomp g (reductionι Y) = NatTrans.vcomp (reductionι X) f) :
    g = mapReduction f :=
  ReductionData.map_unique RX.toReductionData RY.toReductionData f hg

/-- Reduction sends identity morphisms to identity morphisms. -/
theorem mapReduction_id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [RX : Reduction X] :
    mapReduction (𝟙 X) = 𝟙 (reduction X) :=
  ReductionData.map_id RX.toReductionData

/-- Reduction preserves composition. -/
theorem mapReduction_comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [RX : Reduction X] [RY : Reduction Y] [RZ : Reduction Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapReduction (f ≫ g) = mapReduction f ≫ mapReduction g :=
  ReductionData.map_comp RX.toReductionData RY.toReductionData RZ.toReductionData f g

/-- A morphism of formal algebraic spaces is surjective if the induced map of
underlying reduced algebraic spaces is surjective. -/
@[mk_iff]
class Surjective {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) : Prop where
  /-- The induced map of reductions is a surjective morphism of algebraic
  spaces. -/
  map_surjective : AlgebraicSpace.Surjective (mapReduction f)

/-- Surjectivity is equivalent to the predicate on explicit reductions. -/
theorem surjective_iff_reductionData {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [RX : Reduction X] [RY : Reduction Y] (f : X ⟶ Y) :
    Surjective f ↔ ReductionData.Surjective RX.toReductionData RY.toReductionData f :=
  ⟨fun h ↦ h.map_surjective, fun h ↦ ⟨h⟩⟩

/-- On morphisms of algebraic spaces, viewed as formal algebraic spaces via
`instIsFormalAlgebraicSpace_functorOfPoints`, surjectivity agrees with
`AlgebraicSpace.Surjective`. -/
theorem surjective_functorOfPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X.functorOfPoints ⟶ Y.functorOfPoints) :
    Surjective f ↔ AlgebraicSpace.Surjective f :=
  (surjective_iff_reductionData f).trans (ReductionData.surjective_functorOfPoints f)

namespace Surjective

/-- The identity morphism of a formal algebraic space is surjective. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X] : Surjective (𝟙 X) := by
  refine ⟨?_⟩
  rw [mapReduction_id]
  exact AlgebraicSpace.Surjective.id

/-- An isomorphism of formal algebraic spaces is surjective. -/
instance of_isIso {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) [IsIso f] : Surjective f := by
  refine ⟨⟨?_⟩⟩
  intro y
  refine ⟨AlgebraicSpace.Points.map (mapReduction (inv f)) y, ?_⟩
  rw [← AlgebraicSpace.Points.map_comp, ← mapReduction_comp, IsIso.inv_hom_id,
    mapReduction_id, AlgebraicSpace.Points.map_id]

/-- A surjective morphism of algebraic spaces is surjective as a morphism of
formal algebraic spaces, via the functor-of-points reduction. -/
instance ofAlgebraicSpace {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X.functorOfPoints ⟶ Y.functorOfPoints)
    [AlgebraicSpace.Surjective f] : Surjective f :=
  (surjective_functorOfPoints f).mpr inferInstance

/-- A surjective morphism of formal algebraic spaces induces a surjective
morphism of algebraic-space reductions. -/
theorem spec {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) [Surjective f] :
    AlgebraicSpace.Surjective (mapReduction f) :=
  Surjective.map_surjective (f := f)

/-- A morphism of formal algebraic spaces is surjective as soon as the induced
map of algebraic-space reductions is surjective. -/
theorem of {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] {f : X ⟶ Y}
    (hf : AlgebraicSpace.Surjective (mapReduction f)) : Surjective f :=
  ⟨hf⟩

end Surjective

/-- The composition of two surjective morphisms of formal algebraic spaces is
surjective. -/
@[stacks 0GHQ]
instance Surjective.comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [Reduction X] [Reduction Y] [Reduction Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] [Surjective g] :
    Surjective (f ≫ g) := by
  apply Surjective.of
  rw [mapReduction_comp]
  exact @AlgebraicSpace.surjective_comp S _ _ _ (mapReduction f) (mapReduction g)
    (Surjective.spec f) (Surjective.spec g)

end AlgebraicGeometry.FormalAlgebraicSpace
