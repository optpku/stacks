/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dominant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalMap.Basic

/-!
# Dominant rational maps of algebraic spaces

A rational map of algebraic spaces is dominant when every representative
partial map has dominant underlying morphism.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

namespace PartialMap

/-- Dominance of the underlying morphism is invariant under equivalence of partial maps. -/
theorem dominant_hom_iff_of_equiv {f g : PartialMap X Y} (h : f.equiv g) :
    Dominant f.hom ↔ Dominant g.hom :=
  sorry

/-- Restriction of a dominant partial map along a dense open of its domain remains
dominant on the underlying morphism. -/
theorem dominant_restrict_hom {f : PartialMap X Y} [Dominant f.hom]
    {U : smallZariskiSite X} (ιU : U ⟶ f.domain) (hU : IsDense U.hom) :
    Dominant (f.restrict ιU hU).hom :=
  sorry

end PartialMap

/-- A rational map is dominant if every representative partial map has dominant
underlying morphism. -/
@[mk_iff]
class RationalMap.IsDominant (φ : RationalMap X Y) : Prop where
  /-- Every representative is a dominant morphism of algebraic spaces. -/
  any_rep : ∀ f : PartialMap X Y, f.toRationalMap = φ → Dominant f.hom

/-- A partial map with dominant underlying morphism determines a dominant rational map. -/
def instIsDominant_toRationalMap (f : PartialMap X Y) [Dominant f.hom] :
    f.toRationalMap.IsDominant := by
  refine ⟨fun g hg ↦ ?_⟩
  exact (PartialMap.dominant_hom_iff_of_equiv
    (PartialMap.toRationalMap_eq_iff.mp hg)).mpr inferInstance

namespace RationalMap

/-- A rational map is dominant if and only if some representative partial map has
dominant underlying morphism. -/
theorem isDominant_iff_exists (φ : RationalMap X Y) :
    φ.IsDominant ↔ ∃ f : PartialMap X Y, Dominant f.hom ∧ f.toRationalMap = φ := by
  constructor
  · intro h
    obtain ⟨f, hf⟩ := φ.exists_rep
    exact ⟨f, h.any_rep f hf, hf⟩
  · rintro ⟨f, hf, rfl⟩
    exact @instIsDominant_toRationalMap S X Y f hf

end RationalMap

namespace RationalMap.IsDominant

/-- Every representative of a dominant rational map is a dominant morphism. -/
theorem spec {φ : RationalMap X Y} [φ.IsDominant] {f : PartialMap X Y}
    (hf : f.toRationalMap = φ) : Dominant f.hom :=
  RationalMap.IsDominant.any_rep f hf

/-- A rational map is dominant as soon as every representative is a dominant morphism. -/
theorem of {φ : RationalMap X Y}
    (h : ∀ f : PartialMap X Y, f.toRationalMap = φ → Dominant f.hom) :
    φ.IsDominant :=
  ⟨h⟩

end RationalMap.IsDominant

namespace PartialMap

/-- A partial map determines a dominant rational map if and only if its underlying
morphism is dominant. -/
theorem isDominant_toRationalMap_iff (f : PartialMap X Y) :
    f.toRationalMap.IsDominant ↔ Dominant f.hom := by
  constructor
  · intro h
    exact h.any_rep f rfl
  · intro h
    exact @instIsDominant_toRationalMap S X Y f h

end PartialMap

end AlgebraicGeometry.AlgebraicSpace
