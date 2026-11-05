module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Fixed
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded Cochain Complex Categories

@stack 013H
@stack 0159

For a category `C` with zero morphisms, this module defines the bounded-above and bounded
cochain complex categories as full subcategories of `CochainComplex C ℤ`:

* `CochainComplex.Minus C` — bounded-above cochain complexes (`Comp⁻(C)`)
* `CochainComplex.Bounded C` — bounded cochain complexes (`Compᵇ(C)`)

Mathlib already provides the bounded-below variant `CochainComplex.Plus C`.

## Main definitions

* `CochainComplex.minus` — the object property: `∃ n, K.IsStrictlyLE n`.
* `CochainComplex.Minus` — the full subcategory of bounded-above complexes.
* `CochainComplex.bounded` — the object property: `plus ⊓ minus`.
* `CochainComplex.Bounded` — the full subcategory of bounded complexes.

## Main results

* Closure under finite limits, finite colimits, isomorphisms for both variants.
* Shift-stability for both variants.
* Biproduct instances in the preadditive case.
* `ContainsZero` instances.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape

universe v u

namespace CochainComplex

variable (C : Type u) [Category.{v} C]

section

variable [HasZeroMorphisms C]

/-- The object property of bounded-above cochain complexes. -/
@[stacks 013H "bounded-above cochain complexes"]
protected def minus : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ ∃ n : ℤ, K.IsStrictlyLE n

/-- A cochain complex is bounded above exactly when it vanishes in all sufficiently high
degrees. -/
@[stacks 013H "bounded-above cochain complexes"]
lemma minus_iff (K : CochainComplex C ℤ) :
    CochainComplex.minus C K ↔ ∃ n : ℤ, K.IsStrictlyLE n := Iff.rfl

/-- Bounded-above cochain complexes are closed under isomorphisms. -/
instance : (CochainComplex.minus C).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro _ _ e ⟨n, hn⟩
    exact ⟨n, isStrictlyLE_of_iso e n⟩

/-- The category `Comp⁻(C)` of bounded-above cochain complexes. -/
@[stacks 013H "bounded-above cochain complexes"]
abbrev Minus :=
  (CochainComplex.minus C).FullSubcategory

namespace Minus

/-- The inclusion `Comp⁻(C) ⥤ Comp(C)`. -/
abbrev ι : Minus C ⥤ CochainComplex C ℤ :=
  (CochainComplex.minus C).ι

/-- Finite limits of bounded-above cochain complexes are bounded above. -/
instance (J : Type*) [SmallCategory J] [FinCategory J]
    [HasLimitsOfShape J C] :
    (CochainComplex.minus C).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro K ⟨p⟩
    obtain ⟨n, hn⟩ : ∃ n : ℤ, ∀ j : J, (p.diag.obj j).IsStrictlyLE n := by
      choose n hn using p.prop_diag_obj
      refine ⟨Finset.max' (Finset.image n ⊤ ∪ {0}) ⟨0, by simp⟩, fun j ↦ ?_⟩
      have hnj :
          n j ≤ Finset.max' (Finset.image n ⊤ ∪ {0}) ⟨0, by simp⟩ :=
        Finset.le_max' _ _ <| Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_image.mpr ⟨j, by simp, rfl⟩
      -- Local instance justification (proof-local temporary data): the bound supplied by `hn`
      -- varies with `j` and is not canonical.
      haveI := hn j
      exact (p.diag.obj j).isStrictlyLE_of_le _ _ hnj
    refine ⟨n, ?_⟩
    rw [isStrictlyLE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isLimitOfPreserves (HomologicalComplex.eval _ _ i) p.isLimit).hom_ext <| fun j ↦ by
      -- Local instance justification (proof-local temporary data): use the bound witness for the
      -- current component of the finite diagram.
      haveI := hn j
      exact (isZero_of_isStrictlyLE (p.diag.obj j) n i).eq_of_tgt _ _

/-- Finite colimits of bounded-above cochain complexes are bounded above. -/
instance (J : Type*) [SmallCategory J] [FinCategory J]
    [HasColimitsOfShape J C] :
    (CochainComplex.minus C).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro K ⟨p⟩
    obtain ⟨n, hn⟩ : ∃ n : ℤ, ∀ j : J, (p.diag.obj j).IsStrictlyLE n := by
      choose n hn using p.prop_diag_obj
      refine ⟨Finset.max' (Finset.image n ⊤ ∪ {0}) ⟨0, by simp⟩, fun j ↦ ?_⟩
      have hnj :
          n j ≤ Finset.max' (Finset.image n ⊤ ∪ {0}) ⟨0, by simp⟩ :=
        Finset.le_max' _ _ <| Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_image.mpr ⟨j, by simp, rfl⟩
      -- Local instance justification (proof-local temporary data): the bound supplied by `hn`
      -- varies with `j` and is not canonical.
      haveI := hn j
      exact (p.diag.obj j).isStrictlyLE_of_le _ _ hnj
    refine ⟨n, ?_⟩
    rw [isStrictlyLE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isColimitOfPreserves (HomologicalComplex.eval _ _ i) p.isColimit).hom_ext <| fun j ↦ by
      -- Local instance justification (proof-local temporary data): use the bound witness for the
      -- current component of the finite diagram.
      haveI := hn j
      exact (isZero_of_isStrictlyLE (p.diag.obj j) n i).eq_of_src _ _

/-- Bounded-above cochain complexes admit finite limits when the coefficient category does. -/
instance [HasFiniteLimits C] : HasFiniteLimits (Minus C) where
  out J _ _ := by infer_instance

/-- Bounded-above cochain complexes admit finite colimits when the coefficient category does. -/
instance [HasFiniteColimits C] : HasFiniteColimits (Minus C) where
  out J _ _ := by infer_instance

end Minus

/-- The object property of bounded cochain complexes. -/
@[stacks 013H "bounded cochain complexes"]
protected def bounded : ObjectProperty (CochainComplex C ℤ) :=
  CochainComplex.plus C ⊓ CochainComplex.minus C

/-- A cochain complex is bounded exactly when it is both bounded below and bounded above. -/
@[stacks 013H "bounded cochain complexes"]
lemma bounded_iff (K : CochainComplex C ℤ) :
    CochainComplex.bounded C K ↔
      CochainComplex.plus C K ∧ CochainComplex.minus C K := Iff.rfl

/-- The category `Compᵇ(C)` of bounded cochain complexes. -/
@[stacks 013H "bounded cochain complexes"]
abbrev Bounded :=
  (CochainComplex.bounded C).FullSubcategory

namespace Bounded

/-- The inclusion `Compᵇ(C) ⥤ Comp(C)`. -/
abbrev ι : Bounded C ⥤ CochainComplex C ℤ :=
  (CochainComplex.bounded C).ι

/-- Finite limits of bounded cochain complexes are bounded. -/
instance (J : Type*) [SmallCategory J] [FinCategory J]
    [HasLimitsOfShape J C] :
    (CochainComplex.bounded C).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro K ⟨p⟩
    refine ⟨?_, ?_⟩
    · exact (CochainComplex.plus C).prop_of_isLimit p.isLimit fun j ↦ (p.prop_diag_obj j).1
    · exact (CochainComplex.minus C).prop_of_isLimit p.isLimit fun j ↦ (p.prop_diag_obj j).2

/-- Finite colimits of bounded cochain complexes are bounded. -/
instance (J : Type*) [SmallCategory J] [FinCategory J]
    [HasColimitsOfShape J C] :
    (CochainComplex.bounded C).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro K ⟨p⟩
    refine ⟨?_, ?_⟩
    · exact (CochainComplex.plus C).prop_of_isColimit p.isColimit fun j ↦ (p.prop_diag_obj j).1
    · exact (CochainComplex.minus C).prop_of_isColimit p.isColimit fun j ↦ (p.prop_diag_obj j).2

/-- Bounded cochain complexes admit finite limits when the coefficient category does. -/
instance [HasFiniteLimits C] : HasFiniteLimits (Bounded C) where
  out J _ _ := by infer_instance

/-- Bounded cochain complexes admit finite colimits when the coefficient category does. -/
instance [HasFiniteColimits C] : HasFiniteColimits (Bounded C) where
  out J _ _ := by infer_instance

end Bounded

end

section ZeroMembership

variable [Preadditive C] [HasZeroObject C]

/-- The zero cochain complex is bounded below. -/
@[stacks 0159 "zero complex is bounded below"]
theorem zero_mem_plus :
    CochainComplex.plus C (HomologicalComplex.zero : CochainComplex C ℤ) := sorry

/-- The zero cochain complex is bounded above. -/
@[stacks 0159 "zero complex is bounded above"]
theorem zero_mem_minus :
    CochainComplex.minus C (HomologicalComplex.zero : CochainComplex C ℤ) := sorry

/-- The zero cochain complex is bounded. -/
@[stacks 0159 "zero complex is bounded"]
theorem zero_mem_bounded :
    CochainComplex.bounded C (HomologicalComplex.zero : CochainComplex C ℤ) := sorry

/-- The bounded-below object property contains a zero complex. -/
instance plusContainsZero : (CochainComplex.plus C).ContainsZero := sorry

/-- The bounded-above object property contains a zero complex. -/
instance minusContainsZero : (CochainComplex.minus C).ContainsZero := sorry

/-- The bounded object property contains a zero complex. -/
instance boundedContainsZero : (CochainComplex.bounded C).ContainsZero := sorry

end ZeroMembership

section

variable [Preadditive C]

namespace Minus

/-- Bounded-above cochain complexes have finite biproducts when coefficients have finite
colimits. -/
instance [HasFiniteColimits C] : HasFiniteBiproducts (Minus C) :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Bounded-above cochain complexes have binary biproducts when coefficients have finite
colimits. -/
instance [HasFiniteColimits C] : HasBinaryBiproducts (Minus C) :=
  hasBinaryBiproducts_of_finite_biproducts _

/-- Binary biproducts of coefficients induce binary biproducts of bounded-above complexes. -/
@[instance 10] instance [HasBinaryBiproducts C] : HasBinaryBiproducts (Minus C) := by
  -- Local instance justification (defeq pin): select the full-subcategory coproduct instance
  -- before constructing biproducts to avoid search considering the instance being defined.
  let _ : HasBinaryCoproducts (Minus C) := by infer_instance
  exact HasBinaryBiproducts.of_hasBinaryCoproducts

end Minus

/-- Bounded-above cochain complexes remain bounded above under every integer shift. -/
instance : (CochainComplex.minus C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    ⟨fun K ⟨k, hk⟩ ↦ ⟨k - n, K.isStrictlyLE_shift k n _ (by lia)⟩⟩

namespace Bounded

/-- Bounded cochain complexes have finite biproducts when coefficients have finite colimits. -/
instance [HasFiniteColimits C] : HasFiniteBiproducts (Bounded C) :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Bounded cochain complexes have binary biproducts when coefficients have finite colimits. -/
instance [HasFiniteColimits C] : HasBinaryBiproducts (Bounded C) :=
  hasBinaryBiproducts_of_finite_biproducts _

/-- Binary biproducts of coefficients induce binary biproducts of bounded complexes. -/
@[instance 10] instance [HasBinaryBiproducts C] : HasBinaryBiproducts (Bounded C) := by
  -- Local instance justification (defeq pin): select the full-subcategory coproduct instance
  -- before constructing biproducts to avoid search considering the instance being defined.
  let _ : HasBinaryCoproducts (Bounded C) := by infer_instance
  exact HasBinaryBiproducts.of_hasBinaryCoproducts

end Bounded

/-- Bounded cochain complexes remain bounded under every integer shift. -/
instance : (CochainComplex.bounded C).IsStableUnderShift ℤ := by
  refine ⟨fun n ↦ ?_⟩
  refine ⟨fun K hK ↦ ?_⟩
  exact ⟨(CochainComplex.plus C).le_shift n K hK.1,
    (CochainComplex.minus C).le_shift n K hK.2⟩

namespace Plus

/-- Bounded-below cochain complexes have finite biproducts when coefficients have finite
colimits. -/
instance [HasFiniteColimits C] : HasFiniteBiproducts (CochainComplex.Plus C) :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Bounded-below cochain complexes have binary biproducts when coefficients have finite
colimits. -/
instance [HasFiniteColimits C] : HasBinaryBiproducts (CochainComplex.Plus C) :=
  hasBinaryBiproducts_of_finite_biproducts _

/-- Binary biproducts of coefficients induce binary biproducts of bounded-below complexes. -/
@[instance 10] instance [HasBinaryBiproducts C] :
    HasBinaryBiproducts (CochainComplex.Plus C) := by
  -- Local instance justification (defeq pin): select the full-subcategory coproduct instance
  -- before constructing biproducts to avoid search considering the instance being defined.
  let _ : HasBinaryCoproducts (CochainComplex.Plus C) := by infer_instance
  exact HasBinaryBiproducts.of_hasBinaryCoproducts

end Plus

end


end CochainComplex
