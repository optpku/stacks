/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.MappingCone.Bounded
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

@[expose] public section

/-!
# Split-epimorphic mapping-cocone factorizations

This leaf is the dual companion of `SplitMonoFactorization`.  The construction is deliberately
owned by the mapping-cocone object rather than by a chapter: it can be used for arbitrary
preadditive categories with binary biproducts and for any cochain map `α`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {K L : CochainComplex C ℤ}

namespace SplitEpiFactorization

/-- The canonical middle complex for a split-epimorphic factorization of `α : K ⟶ L`. -/
@[stacks 0642 "split-epimorphic mapping-cocone factorization object"]
abbrev obj (K L : CochainComplex C ℤ) : CochainComplex C ℤ :=
  K ⊞ mappingCocone (𝟙 L)

/-- The canonical map from the split-epimorphic factorization object to the target. -/
@[stacks 0642 "split-epimorphic factorization map"]
abbrev desc (α : K ⟶ L) : obj K L ⟶ L :=
  biprod.desc α (mappingCocone.fst (𝟙 L))

/-- The projection from the split-epimorphic factorization object to its source summand. -/
@[stacks 0642 "split-epimorphic factorization projection"]
abbrev projection (K L : CochainComplex C ℤ) : obj K L ⟶ K :=
  biprod.fst

/-- The section of the split-epimorphic factorization projection. -/
@[stacks 0642 "split-epimorphic factorization section"]
abbrev section_ (K L : CochainComplex C ℤ) :
    K ⟶ obj K L :=
  biprod.inl

/-- The shifted mapping-cone map underlying a map of identity mapping-cocones. -/
@[stacks 0642 "map of identity mapping-cocones"]
noncomputable def coconeMapRaw
    {L₁ L₂ : CochainComplex C ℤ} (b : L₁ ⟶ L₂) :
    (mappingCone (𝟙 L₁))⟦(-1 : ℤ)⟧ ⟶ (mappingCone (𝟙 L₂))⟦(-1 : ℤ)⟧ :=
  (CochainComplex.shiftFunctor C (-1)).map
    (X := mappingCone (𝟙 L₁)) (Y := mappingCone (𝟙 L₂))
    ((mappingCone.map (𝟙 L₁) (𝟙 L₂) b b
      ((Category.id_comp b).trans (Category.comp_id b).symm)) :
      mappingCone (𝟙 L₁) ⟶ mappingCone (𝟙 L₂))

/-- The map between identity mapping-cocones induced by a map of their underlying complexes. -/
@[stacks 0642 "map of identity mapping-cocones"]
noncomputable abbrev coconeMap
    {L₁ L₂ : CochainComplex C ℤ} (b : L₁ ⟶ L₂) :
    mappingCocone (𝟙 L₁) ⟶ mappingCocone (𝟙 L₂) :=
  coconeMapRaw b

/-- Maps of the source and target induce a map between split-epimorphic factorization objects. -/
@[stacks 0642 "split-epimorphic factorization map"]
noncomputable def map
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) :
    obj K₁ L₁ ⟶ obj K₂ L₂ :=
  biprod.map a (coconeMap b)

/-- The map of split-epimorphic factorization objects induced by identities is the identity. -/
@[simp, stacks 0642]
theorem map_id (K L : CochainComplex C ℤ) :
    map (𝟙 K) (𝟙 L) = 𝟙 (obj K L) := sorry

/-- Maps of split-epimorphic factorization objects respect composition. -/
@[stacks 0642]
theorem map_comp
    {K₁ L₁ K₂ L₂ K₃ L₃ : CochainComplex C ℤ}
    (a₁ : K₁ ⟶ K₂) (b₁ : L₁ ⟶ L₂)
    (a₂ : K₂ ⟶ K₃) (b₂ : L₂ ⟶ L₃) :
    map (a₁ ≫ a₂) (b₁ ≫ b₂) = map a₁ b₁ ≫ map a₂ b₂ := sorry

/-- The source projection is natural with respect to maps of factorization objects. -/
@[simp, stacks 0642]
theorem map_comp_projection
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) :
    map a b ≫ projection K₂ L₂ = projection K₁ L₁ ≫ a := sorry

/-- The source section is natural with respect to maps of factorization objects. -/
@[simp, stacks 0642]
theorem section_comp_map
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) :
    section_ K₁ L₁ ≫ map a b = a ≫ section_ K₂ L₂ := sorry

/-- The factorization map is natural with respect to a commuting square of cochain maps. -/
@[stacks 0642]
theorem desc_naturality
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    {α₁ : K₁ ⟶ L₁} {α₂ : K₂ ⟶ L₂}
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h : α₁ ≫ b = a ≫ α₂) :
    map a b ≫ desc α₂ = desc α₁ ≫ b := sorry

/-- The canonical section followed by the projection is the identity on the source summand. -/
@[simp, stacks 0642 "projection-section computation"]
theorem section_comp_projection (K L : CochainComplex C ℤ) :
    section_ K L ≫ projection K L = 𝟙 K := sorry

/-- The explicit homotopy from the projection-section composite to the identity of the
split-epimorphic factorization object. -/
noncomputable def coconeHomotopy
    (L : CochainComplex C ℤ) : Homotopy (𝟙 (mappingCocone (𝟙 L))) 0 where
  hom := (mappingCone.homotopyToZeroOfId L).shift (-1) |>.hom
  zero := sorry
  comm := sorry

/-- The biproduct projection followed by its section and the contractible summand add to the
identity. -/
@[stacks 0642 "projection-section computation"]
theorem projection_section_sum
    (K L : CochainComplex C ℤ) :
    (projection K L ≫ section_ K L) +
        ((biprod.snd : obj K L ⟶ mappingCocone (𝟙 L)) ≫
          𝟙 (mappingCocone (𝟙 L)) ≫
          (biprod.inr : mappingCocone (𝟙 L) ⟶ obj K L)) =
      𝟙 (obj K L) := sorry

/-- The zero end of the contracted summand contributes nothing to the biproduct projection. -/
@[stacks 0642 "projection-section zero computation"]
theorem projection_section_zero
    (K L : CochainComplex C ℤ) :
    (projection K L ≫ section_ K L) +
        ((biprod.snd : obj K L ⟶ mappingCocone (𝟙 L)) ≫
          (0 : mappingCocone (𝟙 L) ⟶ mappingCocone (𝟙 L)) ≫
          (biprod.inr : mappingCocone (𝟙 L) ⟶ obj K L)) =
      projection K L ≫ section_ K L := sorry

/-- The projection-section composite contracts the mapping-cocone summand. -/
@[stacks 0642 "split-epimorphic factorization contraction"]
noncomputable def projectionHomotopy
    (K L : CochainComplex C ℤ) :
    Homotopy
      (projection K L ≫ section_ K L)
      (𝟙 (obj K L)) :=
  let q : obj K L ⟶ mappingCocone (𝟙 L) := biprod.snd
  let j : mappingCocone (𝟙 L) ⟶ obj K L := biprod.inr
  let h₁ := (coconeHomotopy L).compRight j |>.compLeft q
  let h₂ := Homotopy.add
    (Homotopy.refl (projection K L ≫ section_ K L)) h₁
  (Homotopy.ofEq (projection_section_zero K L).symm).trans
    (h₂.symm.trans (Homotopy.ofEq (projection_section_sum K L)))

/-- The factorization object retracts onto `K` in the homotopy category. -/
@[stacks 0642 "split-epimorphic factorization homotopy equivalence"]
noncomputable def homotopyEquiv (K L : CochainComplex C ℤ) :
    HomotopyEquiv (obj K L) K where
  hom := projection K L
  inv := section_ K L
  homotopyHomInvId := projectionHomotopy K L
  homotopyInvHomId := Homotopy.ofEq (section_comp_projection K L)

/-- Every component of the canonical split-epimorphic factorization map is split epic. -/
@[stacks 0642 "termwise split epimorphism of the factorization map"]
theorem desc_f_isSplitEpi (α : K ⟶ L) (n : ℤ) :
    IsSplitEpi ((desc α).f n) := sorry

/-- The factorization map restricts to the original map on the first biproduct summand. -/
@[simp, stacks 0642 "factorization map on the first summand"]
theorem section_comp_desc (α : K ⟶ L) :
    section_ K L ≫ desc α = α := sorry

/-- Source-compatible name for the split-epimorphic factorization package. -/
@[stacks 0642]
theorem factorization_spec (α : K ⟶ L) :
    ∃ _ : Homotopy
        (projection K L ≫ section_ K L)
        (𝟙 (obj K L)),
      (∀ n : ℤ, IsSplitEpi ((desc α).f n)) ∧
        section_ K L ≫ desc α = α ∧
        section_ K L ≫ projection K L = 𝟙 K := sorry

/-- The shifted identity mapping cocone preserves bounded-below complexes. -/
@[stacks 0642]
theorem cocone_id_plus (hL : CochainComplex.plus C L) :
    CochainComplex.plus C (mappingCocone (𝟙 L)) := sorry

/-- The shifted identity mapping cocone preserves bounded-above complexes. -/
@[stacks 0642]
theorem cocone_id_bounded_above (hL : CochainComplex.minus C L) :
    CochainComplex.minus C (mappingCocone (𝟙 L)) := sorry

/-- The split-epimorphic factorization object is bounded below when both inputs are. -/
@[stacks 0642]
theorem plus
    (hK : CochainComplex.plus C K) (hL : CochainComplex.plus C L) :
    CochainComplex.plus C (obj K L) := sorry

/-- The split-epimorphic factorization object is bounded above when both inputs are. -/
@[stacks 0642]
theorem bounded_above
    (hK : CochainComplex.minus C K) (hL : CochainComplex.minus C L) :
    CochainComplex.minus C (obj K L) := sorry

/-- The split-epimorphic factorization object is bounded when both inputs are. -/
@[stacks 0642]
theorem bounded
    (hK : CochainComplex.bounded C K) (hL : CochainComplex.bounded C L) :
    CochainComplex.bounded C (obj K L) := sorry

end SplitEpiFactorization

end CochainComplex
