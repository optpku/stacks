/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Total complexes and the flip functor

Mathlib constructs totals of `K.flip`, but the object of `flipFunctor` is deliberately not
transparent enough for typeclass search to reuse that instance.  This file provides the
canonical functor-object bridge.
-/

@[expose] public section

open CategoryTheory

universe v u w₁ w₂ w

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {I₁ : Type w₁} {I₂ : Type w₂} {J : Type w}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c : ComplexShape J}
variable [TotalComplexShape c₁ c₂ c] [TotalComplexShape c₂ c₁ c]
variable [TotalComplexShapeSymmetry c₁ c₂ c]

/-- Typeclass-search bridge from a total of `K` to a total of the object obtained by applying
the flip functor to `K`. -/
@[stacks 0130 "total existence after flipping a double complex"]
instance flipFunctor_obj_hasTotal
    (K : HomologicalComplex₂ C c₁ c₂) [K.HasTotal c] :
    ((flipFunctor C c₁ c₂).obj K).HasTotal c :=
  inferInstanceAs (K.flip.HasTotal c)

section Functor

variable [DecidableEq J]
variable [∀ K : HomologicalComplex₂ C c₁ c₂, K.HasTotal c]
variable [∀ K : HomologicalComplex₂ C c₂ c₁, K.HasTotal c]

/-- The total-flip comparison is natural in maps of double complexes. -/
theorem totalFlipIso_naturality
    {K L : HomologicalComplex₂ C c₁ c₂} (f : K ⟶ L) :
    total.map ((flipFunctor C c₁ c₂).map f) c ≫ (L.totalFlipIso c).hom =
      (K.totalFlipIso c).hom ≫ total.map f c := sorry

/-- The inverse total-flip comparison is natural in maps of double complexes. -/
@[reassoc, stacks 0130 "inverse naturality of totalization symmetry"]
theorem totalFlipIso_inv_naturality
    {K L : HomologicalComplex₂ C c₁ c₂} (f : K ⟶ L) :
    total.map f c ≫ (L.totalFlipIso c).inv =
      (K.totalFlipIso c).inv ≫ total.map ((flipFunctor C c₁ c₂).map f) c := sorry

/-- Conjugating the direct total map by the total-flip comparisons recovers the flipped total
map. -/
@[reassoc, stacks 0130 "source-map computation for totalization symmetry"]
theorem totalFlipIso_source_map
    {K L : HomologicalComplex₂ C c₁ c₂} (f : K ⟶ L) :
    (K.totalFlipIso c).hom ≫ total.map f c ≫ (L.totalFlipIso c).inv =
      total.map ((flipFunctor C c₁ c₂).map f) c := sorry

/-- Conjugating the flipped total map by the inverse total-flip comparisons recovers the direct
total map. -/
@[reassoc, stacks 0130 "target-map computation for totalization symmetry"]
theorem totalFlipIso_target_map
    {K L : HomologicalComplex₂ C c₁ c₂} (f : K ⟶ L) :
    (K.totalFlipIso c).inv ≫
        total.map ((flipFunctor C c₁ c₂).map f) c ≫ (L.totalFlipIso c).hom =
      total.map f c := sorry

/-- Flipping a double complex before totalization is naturally isomorphic to totalizing it
directly. -/
@[stacks 0130 "symmetry of totalization as a natural isomorphism"]
noncomputable def totalFlipNatIso :
    flipFunctor C c₁ c₂ ⋙ totalFunctor C c₂ c₁ c ≅ totalFunctor C c₁ c₂ c :=
  NatIso.ofComponents (fun K ↦ K.totalFlipIso c)
    (fun f ↦ totalFlipIso_naturality f)

end Functor

end HomologicalComplex₂
