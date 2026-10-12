/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Presheaf.Subfunctor
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] {F G : Presheaf C} (φ : F ⟶ G)

/-
Definition 7.3.5: notation as in Lemma 7.3.4. The unique subpresheaf G' of G
through which a map of presheaves of sets φ : F ⟶ G factors by a surjective
first map is called the image of φ. This is the subfunctor Subfunctor.range φ,
with (range φ).obj U = Set.range (φ.app U).
-/
@[stacks 00VA] #check (CategoryTheory.Subfunctor.epiFactorization_iff_range φ :
  ∀ H : Subfunctor G,
    (∃ α : F ⟶ H.toFunctor, Epi α ∧ α ≫ H.ι = φ) ↔ H = Subfunctor.range φ)

#check Subfunctor.range φ

#check Subfunctor.toRange φ
#check Subfunctor.toRange_ι
