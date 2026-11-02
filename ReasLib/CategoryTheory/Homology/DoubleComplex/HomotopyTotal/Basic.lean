/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.HomotopyCategory.Lift
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Additive
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalHomotopy.Flip

/-!
# Totalization of double complexes on homotopy categories

The raw totalization functor and its composite with the double-complex flip both preserve
homotopy. Hence they descend from the homotopy category of complexes of cochain complexes to the
homotopy category of cochain complexes.

The names `direct` and `flipped` describe the formal implementation. This avoids conflating the
two formal coordinates with the textbook conventions for first and second totalization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomotopyCategory

noncomputable section

universe v u

namespace HomologicalComplex₂.HomotopyTotal

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasCountableCoproducts C]

/-- Raw coproduct totalization of cochain double complexes. -/
noncomputable abbrev rawDirect :
    HomologicalComplex₂ C (up ℤ) (up ℤ) ⥤ CochainComplex C ℤ :=
  totalFunctor C (up ℤ) (up ℤ) (up ℤ)

/-- Raw totalization after exchanging the two coordinates of a cochain double complex. -/
noncomputable abbrev rawFlipped :
    HomologicalComplex₂ C (up ℤ) (up ℤ) ⥤ CochainComplex C ℤ :=
  flipFunctor C (up ℤ) (up ℤ) ⋙ rawDirect C

/-- Flipped raw totalization is naturally isomorphic to direct raw totalization. -/
noncomputable def rawFlippedIsoDirect : rawFlipped C ≅ rawDirect C :=
  totalFlipNatIso

/-- Direct raw totalization preserves homotopies of double-complex maps. -/
theorem rawDirectPreservesHomotopy : (rawDirect C).PreservesHomotopy := by
  rintro K L f g ⟨h⟩
  exact ⟨Total.Homotopy.First.of h⟩

/-- Flipped raw totalization preserves homotopies of double-complex maps. -/
theorem rawFlippedPreservesHomotopy : (rawFlipped C).PreservesHomotopy := by
  intro K L f g h
  obtain ⟨h⟩ := rawDirectPreservesHomotopy C h
  let e := rawFlippedIsoDirect C
  have conjugate (a : K ⟶ L) :
      (e.hom.app K ≫ (rawDirect C).map a) ≫ e.inv.app L =
        (rawFlipped C).map a := by
    rw [← e.hom.naturality a]
    simp
  exact ⟨(Homotopy.ofEq (conjugate f).symm).trans
    (((h.compLeft (e.hom.app K)).compRight (e.inv.app L)).trans
      (Homotopy.ofEq (conjugate g)))⟩

/-- Direct totalization descended to homotopy categories. -/
@[stacks 0G6D "direct totalization on homotopy categories"]
noncomputable def direct :
    HomotopyCategory (CochainComplex C ℤ) (up ℤ) ⥤ HomotopyCategory C (up ℤ) :=
  CategoryTheory.Functor.Homotopy.lift (rawDirect C) (rawDirectPreservesHomotopy C)

/-- Totalization after exchanging the double-complex coordinates, descended to homotopy
categories. -/
@[stacks 0G6D "flipped totalization on homotopy categories"]
noncomputable def flipped :
    HomotopyCategory (CochainComplex C ℤ) (up ℤ) ⥤ HomotopyCategory C (up ℤ) :=
  CategoryTheory.Functor.Homotopy.lift (rawFlipped C) (rawFlippedPreservesHomotopy C)

/-- Direct descended totalization is additive. -/
instance directAdditive : (direct C).Additive :=
  CategoryTheory.Functor.Homotopy.liftAdditive _ _

/-- Flipped descended totalization is additive. -/
instance flippedAdditive : (flipped C).Additive :=
  CategoryTheory.Functor.Homotopy.liftAdditive _ _

/-- The raw total-flip comparison descends to the two totalization functors on homotopy
categories. -/
noncomputable def flippedIsoDirect : flipped C ≅ direct C :=
  CategoryTheory.Functor.Homotopy.liftIso
    (rawFlippedPreservesHomotopy C) (rawDirectPreservesHomotopy C)
    (rawFlippedIsoDirect C)

/-- Direct totalization factors raw totalization followed by the cochain homotopy quotient. -/
noncomputable def directFactors :
    HomotopyCategory.quotient (CochainComplex C ℤ) (up ℤ) ⋙ direct C ≅
      rawDirect C ⋙ HomotopyCategory.quotient C (up ℤ) :=
  CategoryTheory.Functor.Homotopy.liftFactors _ (rawDirectPreservesHomotopy C)

/-- Flipped totalization factors flipped raw totalization followed by the cochain homotopy
quotient. -/
noncomputable def flippedFactors :
    HomotopyCategory.quotient (CochainComplex C ℤ) (up ℤ) ⋙ flipped C ≅
      rawFlipped C ⋙ HomotopyCategory.quotient C (up ℤ) :=
  CategoryTheory.Functor.Homotopy.liftFactors _ (rawFlippedPreservesHomotopy C)

/-- Direct totalization computes on quotient objects by raw totalization. -/
@[simp]
theorem direct_obj (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) :
    (direct C).obj ((HomotopyCategory.quotient (CochainComplex C ℤ) (up ℤ)).obj K) =
      (HomotopyCategory.quotient C (up ℤ)).obj ((rawDirect C).obj K) := rfl

/-- Direct totalization computes on quotient maps by raw totalization. -/
@[simp]
theorem direct_map {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (f : K ⟶ L) :
    (direct C).map ((HomotopyCategory.quotient (CochainComplex C ℤ) (up ℤ)).map f) =
      (HomotopyCategory.quotient C (up ℤ)).map ((rawDirect C).map f) := rfl

/-- Flipped totalization computes on quotient objects by flipped raw totalization. -/
@[simp]
theorem flipped_obj (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) :
    (flipped C).obj ((HomotopyCategory.quotient (CochainComplex C ℤ) (up ℤ)).obj K) =
      (HomotopyCategory.quotient C (up ℤ)).obj ((rawFlipped C).obj K) := rfl

/-- Flipped totalization computes on quotient maps by flipped raw totalization. -/
@[simp]
theorem flipped_map {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (f : K ⟶ L) :
    (flipped C).map ((HomotopyCategory.quotient (CochainComplex C ℤ) (up ℤ)).map f) =
      (HomotopyCategory.quotient C (up ℤ)).map ((rawFlipped C).map f) := rfl

/-- On a quotient object, the comparison from flipped to direct totalization is induced by the
canonical total-flip isomorphism. -/
@[simp]
theorem flippedIsoDirect_hom_app (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) :
    (flippedIsoDirect C).hom.app
        ((HomotopyCategory.quotient (CochainComplex C ℤ) (up ℤ)).obj K) =
      (HomotopyCategory.quotient C (up ℤ)).map (K.totalFlipIso (up ℤ)).hom := by
  change 𝟙 _ ≫ (HomotopyCategory.quotient C (up ℤ)).map
    (K.totalFlipIso (up ℤ)).hom ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

end HomologicalComplex₂.HomotopyTotal
