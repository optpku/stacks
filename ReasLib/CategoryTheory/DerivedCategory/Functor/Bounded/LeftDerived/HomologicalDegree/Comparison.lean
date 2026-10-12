/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Comparison.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.HomologicalDegree.Naturality
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Localization-Model Comparisons for Left-Derived Homological Degrees

This leaf specializes the integer-degree model comparison at `-n`. It gives
downstream users a direct `Lₙ` interface without repeated integer coercions or
sign bookkeeping.
-/

open CategoryTheory
open scoped CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.LeftDerived.homologicalDegree

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- The localization-model and canonical-single definitions of `Lₙ` are
canonically isomorphic. -/
@[stacks 015A "bounded-above left-derived homological-degree model comparison"]
noncomputable abbrev fromHomotopyIso
    (LF : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B) (n : ℕ) :
    (LeftDerived.degree.fromHomotopy.modelFunctor (-(n : ℤ))).obj LF ≅
      LeftDerived.homologicalDegree LF n :=
  LeftDerived.degree.fromHomotopyIso LF (-(n : ℤ))

namespace fromHomotopy

/-- Localization-model evaluation in homological degree `n` is functorial in
the chosen bounded-above left-derived model. -/
@[stacks 015A "localization-model left-derived homological-degree functor"]
noncomputable abbrev modelFunctor (n : ℕ) :
    (DerivedCategory.Minus A ⥤ DerivedCategory.Minus B) ⥤ A ⥤ B :=
  LeftDerived.degree.fromHomotopy.modelFunctor (-(n : ℤ))

/-- A transformation of left-derived models acts on localization-model
homological degrees. -/
@[stacks 015A "naturality of localization-model left-derived homological degrees"]
noncomputable abbrev map
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (τ : LF ⟶ LG) (n : ℕ) :
    (modelFunctor n).obj LF ⟶ (modelFunctor n).obj LG :=
  LeftDerived.degree.fromHomotopy.map τ (-(n : ℤ))

/-- Localization-model homological-degree maps preserve identities. -/
@[simp]
theorem map_id
    (LF : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B) (n : ℕ) :
    map (𝟙 LF) n = 𝟙 ((modelFunctor n).obj LF) := sorry

/-- Localization-model homological-degree maps preserve composition. -/
@[simp]
theorem map_comp
    {LF LG LH : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (τ : LF ⟶ LG) (σ : LG ⟶ LH) (n : ℕ) :
    map (τ ≫ σ) n = map τ n ≫ map σ n := sorry

/-- An isomorphism of left-derived models acts on localization-model
homological degrees. -/
@[stacks 015A "localization-model left-derived homological-degree isomorphism"]
noncomputable abbrev mapIso
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (e : LF ≅ LG) (n : ℕ) :
    (modelFunctor n).obj LF ≅ (modelFunctor n).obj LG :=
  LeftDerived.degree.fromHomotopy.mapIso e (-(n : ℤ))

/-- The natural comparison between localization-model and canonical
homological degrees. -/
@[stacks 015A "natural comparison of left-derived homological-degree models"]
noncomputable abbrev iso (n : ℕ) :
    modelFunctor (A := A) (B := B) n ≅
      LeftDerived.homologicalDegree.modelFunctor n :=
  LeftDerived.degree.fromHomotopy.iso (-(n : ℤ))

/-- The component of the homological-degree model comparison is
`fromHomotopyIso`. -/
@[simp]
theorem iso_app
    (LF : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B) (n : ℕ) :
    (iso (A := A) (B := B) n).app LF = fromHomotopyIso LF n := sorry

namespace iso

/-- The forward `Lₙ` model comparison is natural in the chosen left-derived
model. -/
@[reassoc, stacks 015A "naturality of the left-derived homological model comparison"]
theorem hom_naturality
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (τ : LF ⟶ LG) (n : ℕ) :
    map τ n ≫ (fromHomotopyIso LG n).hom =
      (fromHomotopyIso LF n).hom ≫
        LeftDerived.homologicalDegree.map τ n := sorry

/-- The inverse `Lₙ` model comparison is natural in the chosen left-derived
model. -/
@[reassoc, stacks 015A "naturality of the inverse left-derived homological model comparison"]
theorem inv_naturality
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (τ : LF ⟶ LG) (n : ℕ) :
    LeftDerived.homologicalDegree.map τ n ≫
        (fromHomotopyIso LG n).inv =
      (fromHomotopyIso LF n).inv ≫ map τ n := sorry

end iso

end fromHomotopy

end CategoryTheory.Functor.LeftDerived.homologicalDegree
