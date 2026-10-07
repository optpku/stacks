module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Nonnegative complexes in the derived category

Extension by zero along the canonical embedding `ℕ → ℤ`, followed by the localization functor,
gives the direct realization of a nonnegative cochain complex in the derived category.  The
construction is independent of bounded-category presentations and applies in every abelian
category with a chosen derived category.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CochainComplex.Nat

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Extension by zero of a nonnegative cochain complex, viewed in the derived category. -/
@[stacks 01GY "derived realization of a nonnegative cochain complex"]
noncomputable def toDerived : CochainComplex C ℕ ⥤ DerivedCategory C :=
  ComplexShape.embeddingUpNat.extendFunctor C ⋙ DerivedCategory.Q

/-- The derived realization is represented by the canonical extension-by-zero complex. -/
@[simp]
theorem toDerived_obj (K : CochainComplex C ℕ) :
    (toDerived C).obj K =
      DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat) := sorry

/-- The derived realization sends a cochain map to the localization of its extension by zero. -/
@[simp]
theorem toDerived_map {K L : CochainComplex C ℕ} (phi : K ⟶ L) :
    (toDerived C).map phi =
      DerivedCategory.Q.map
        (HomologicalComplex.extendMap phi ComplexShape.embeddingUpNat) := sorry

end CochainComplex.Nat
