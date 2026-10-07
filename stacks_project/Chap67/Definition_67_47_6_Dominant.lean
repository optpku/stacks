module

public import stacks_project.Chap67.Definition_67_18_1_Dominant
public import stacks_project.Chap67.Definition_67_47_3_RationalMap

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
instance instIsDominant_toRationalMap (f : PartialMap X Y) [Dominant f.hom] :
    f.toRationalMap.IsDominant :=
  sorry

namespace RationalMap

/-- A rational map is dominant if and only if some representative partial map has
dominant underlying morphism. -/
theorem isDominant_iff_exists (φ : RationalMap X Y) :
    φ.IsDominant ↔ ∃ f : PartialMap X Y, Dominant f.hom ∧ f.toRationalMap = φ :=
  sorry

end RationalMap

namespace RationalMap.IsDominant

/-- Every representative of a dominant rational map is a dominant morphism. -/
theorem spec {φ : RationalMap X Y} [φ.IsDominant] {f : PartialMap X Y}
    (hf : f.toRationalMap = φ) : Dominant f.hom :=
  sorry

/-- A rational map is dominant as soon as every representative is a dominant morphism. -/
theorem of {φ : RationalMap X Y}
    (h : ∀ f : PartialMap X Y, f.toRationalMap = φ → Dominant f.hom) :
    φ.IsDominant :=
  sorry

end RationalMap.IsDominant

namespace PartialMap

/-- A partial map determines a dominant rational map if and only if its underlying
morphism is dominant. -/
theorem isDominant_toRationalMap_iff (f : PartialMap X Y) :
    f.toRationalMap.IsDominant ↔ Dominant f.hom :=
  sorry

end PartialMap

end AlgebraicGeometry.AlgebraicSpace
