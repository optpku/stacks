module

public import Mathlib.CategoryTheory.Comma.Over.OverClass
public import stacks_project.Chap65.Definition_65_12_6_Site
public import stacks_project.Chap67.Definition_67_47_3_RationalMap

/-!
# Morphisms over a base for rational maps of algebraic spaces

A partial map of algebraic spaces is a morphism over `B` when its underlying
morphism commutes with the structure morphisms to `B`. A rational map is a
`B`-rational map when some representative partial map is a morphism over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The structure morphism of an open subspace of `X` over `B` is the composite of the
open immersion with `X ↘ B`. -/
instance instOverClass_smallZariskiSite_left {B : AlgebraicSpace S} [OverClass X B]
    (U : smallZariskiSite X) : OverClass U.left B where
  hom := U.hom ≫ X ↘ B

namespace PartialMap

/-- A partial map is a morphism over `B` when its underlying morphism is a morphism over `B`. -/
abbrev IsOver (B : AlgebraicSpace S) [OverClass X B] [OverClass Y B] (f : PartialMap X Y) : Prop :=
  HomIsOver f.hom B

/-- A partial map is over `B` if and only if the triangle with the structure morphisms of `X`
and `Y` over `B` commutes. -/
theorem isOver_iff {B : AlgebraicSpace S} [OverClass X B] [OverClass Y B] {f : PartialMap X Y} :
    f.IsOver B ↔ f.hom ≫ Y ↘ B = f.domain.hom ≫ X ↘ B :=
  sorry

end PartialMap

/-- A rational map from `X` to `Y` is a `B`-rational map if some representative partial map
is a morphism over `B`. -/
class RationalMap.IsOver (B : AlgebraicSpace S) [OverClass X B] [OverClass Y B]
    (φ : RationalMap X Y) : Prop where
  /-- Some representative is a morphism over `B`. -/
  exists_partialMap_over : ∃ g : PartialMap X Y, g.IsOver B ∧ g.toRationalMap = φ

/-- A partial map over `B` determines a `B`-rational map. -/
instance instIsOver_toRationalMap {B : AlgebraicSpace S} [OverClass X B] [OverClass Y B]
    (f : PartialMap X Y) [f.IsOver B] : f.toRationalMap.IsOver B :=
  ⟨f, inferInstance, rfl⟩

/-- A `B`-rational map has a representative that is a morphism over `B`. -/
theorem RationalMap.exists_partialMap_over {B : AlgebraicSpace S} [OverClass X B] [OverClass Y B]
    (φ : RationalMap X Y) [φ.IsOver B] :
    ∃ g : PartialMap X Y, g.IsOver B ∧ g.toRationalMap = φ :=
  sorry

/-- A rational map is a `B`-rational map if and only if it has a partial-map representative
that is a morphism over `B`. -/
theorem RationalMap.isOver_iff_exists_partialMap_over {B : AlgebraicSpace S}
    [OverClass X B] [OverClass Y B] (φ : RationalMap X Y) :
    φ.IsOver B ↔ ∃ f : PartialMap X Y, f.IsOver B ∧ f.toRationalMap = φ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

