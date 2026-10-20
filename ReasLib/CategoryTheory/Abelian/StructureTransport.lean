module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-! # Uniqueness and transport of abelian category structures -/

@[expose] public section

namespace CategoryTheory

open Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- Any two abelian structures on a fixed category are equal. -/
theorem Abelian.structure_eq (a b : Abelian C) : a = b := by
  have h : a.toPreadditive = b.toPreadditive :=
    @Subsingleton.elim (Preadditive C)
      (@subsingleton_preadditive_of_hasBinaryBiproducts C _
        (@Preadditive.preadditiveHasZeroMorphisms C _ a.toPreadditive)
        (@Abelian.hasBinaryBiproducts C _ a)) _ _
  cases a
  cases b
  cases h
  rfl

/-- An abelian category has homology for any choice of zero morphisms. -/
instance categoryWithHomology_of_abelian_zeroMorphisms
    [a : Abelian C] [z : HasZeroMorphisms C] : CategoryWithHomology C := by
  have h : @Preadditive.preadditiveHasZeroMorphisms C _ a.toPreadditive = z :=
    Subsingleton.elim _ _
  exact h ▸ (@categoryWithHomology_of_abelian C _ a)

end CategoryTheory
