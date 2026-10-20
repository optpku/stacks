/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiSite.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalMap.Basic

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

namespace PartialMap

/-- A partial map is a morphism over `B` when its underlying morphism is a morphism over `B`. -/
abbrev IsOver (B : AlgebraicSpace S) [OverClass X B] [OverClass Y B] (f : PartialMap X Y) : Prop :=
  HomIsOver f.hom B

/-- A partial map is over `B` if and only if the triangle with the structure morphisms of `X`
and `Y` over `B` commutes. -/
theorem isOver_iff {B : AlgebraicSpace S} [OverClass X B] [OverClass Y B] {f : PartialMap X Y} :
    f.IsOver B ↔ f.hom ≫ Y ↘ B = f.domain.hom ≫ X ↘ B :=
  ⟨fun h ↦ h.comp_over, fun h ↦ ⟨h⟩⟩

end PartialMap

/-- A rational map from `X` to `Y` is a `B`-rational map if some representative partial map
is a morphism over `B`. -/
class RationalMap.IsOver (B : AlgebraicSpace S) [OverClass X B] [OverClass Y B]
    (φ : RationalMap X Y) : Prop where
  /-- Some representative is a morphism over `B`. -/
  exists_partialMap_over : ∃ g : PartialMap X Y, g.IsOver B ∧ g.toRationalMap = φ

/-- A partial map over `B` determines a `B`-rational map. -/
def instIsOver_toRationalMap {B : AlgebraicSpace S} [OverClass X B] [OverClass Y B]
    (f : PartialMap X Y) [f.IsOver B] : f.toRationalMap.IsOver B :=
  ⟨f, inferInstance, rfl⟩

/-- A `B`-rational map has a representative that is a morphism over `B`. -/
theorem RationalMap.exists_partialMap_over {B : AlgebraicSpace S} [OverClass X B] [OverClass Y B]
    (φ : RationalMap X Y) [φ.IsOver B] :
    ∃ g : PartialMap X Y, g.IsOver B ∧ g.toRationalMap = φ :=
  RationalMap.IsOver.exists_partialMap_over

/-- A rational map is a `B`-rational map if and only if it has a partial-map representative
that is a morphism over `B`. -/
theorem RationalMap.isOver_iff_exists_partialMap_over {B : AlgebraicSpace S}
    [OverClass X B] [OverClass Y B] (φ : RationalMap X Y) :
    φ.IsOver B ↔ ∃ f : PartialMap X Y, f.IsOver B ∧ f.toRationalMap = φ :=
  ⟨fun h ↦ h.exists_partialMap_over, fun h ↦ ⟨h⟩⟩

end AlgebraicGeometry.AlgebraicSpace

