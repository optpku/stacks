module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.CategoryTheory.Filtration.Complex.Cochain
public import ReasLib.CategoryTheory.Filtration.Exhaustive
public import ReasLib.CategoryTheory.Pretriangulated.CompactObject.Resolution
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Generation of the derived category of modules by the regular module

Every cochain complex of modules has an exhaustive split filtered model whose
graded pieces are coproducts of shifts of the regular module.  Consequently,
the degree-zero regular module weakly generates the unbounded derived category.

@stack 09PB
-/

noncomputable section

open CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe u

-- Local instance justification (instance diamond): all degree-zero embeddings and shifts below
-- use Mathlib's standard derived-category presentation.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModuleCat

variable {R : Type u} [Ring R]

/-- The regular `R`-module placed in cohomological degree zero. -/
@[stacks 09PB "degree-zero regular module"]
abbrev ringSingle (R : Type u) [Ring R] : DerivedCategory (ModuleCat R) :=
  ModuleCat.single0 (ModuleCat.of R R)

/-- The comparison between consecutive negative filtration indices. -/
@[stacks 09PB "successive negative filtration indices"]
theorem negSucc_le_neg (i : ℕ) :
    -((i + 1 : ℕ) : ℤ) ≤ -((i : ℕ) : ℤ) := sorry

/-- Remark 15.59.11 (1): every cochain complex admits a quasi-isomorphic exhaustive filtered
model with termwise split successor maps and graded pieces that are coproducts of shifts of
the regular module. -/
@[stacks 09PB "Remark 15.59.11 (1)"]
theorem exists_splitFilteredModel (M : CochainComplex (ModuleCat R) ℤ) :
    ∃ (P : FilteredCochainComplex (ModuleCat.{u} R)) (π : P.underlying ⟶ M),
      QuasiIso π ∧
      IsZero (P.stage (1 : ℤ)) ∧
      (∀ n : ℤ, ((P.X n).filtration).IsExhaustive) ∧
      (∀ i : ℕ, ∀ n : ℤ,
        IsSplitMono ((P.stageComparison (negSucc_le_neg i)).f n)) ∧
      (∀ i : ℕ, ∃ (J : Type u) (shift : J → ℤ),
        Nonempty
          (P.gradedPiece (-((i : ℕ) : ℤ)) ≅
            ∐ fun j : J ↦
              (CochainComplex.singleFunctor (ModuleCat R) (shift j)).obj
                (ModuleCat.of R R))) := sorry

/-- Remark 15.59.11 (2): the filtered model yields the standard homotopy-colimit distinguished
triangle, packaged as a generating-family resolution by coproducts of shifts of `R[0]`. -/
@[stacks 09PB "Remark 15.59.11 (2), homotopy-colimit distinguished triangle"]
theorem ringSingleResolution_nonempty
    [HasCoproducts (DerivedCategory (ModuleCat R))]
    (M : DerivedCategory (ModuleCat R)) :
    Nonempty (GeneratingFamilyResolution (fun _ : Unit ↦ ringSingle R) M) := sorry

/-- Remark 15.59.11 (3): a property of derived modules that is stable under coproducts and
distinguished triangles and holds for every shift of `R[0]` holds for every object. -/
@[stacks 09PB "Remark 15.59.11 (3)"]
theorem allDerivedObjects_of_coproducts_triangles_ringShifts
    (T : ObjectProperty (DerivedCategory (ModuleCat R)))
    [∀ ι : Type u, T.IsClosedUnderColimitsOfShape (Discrete ι)]
    (h₁ : ∀ {Δ : Triangle (DerivedCategory (ModuleCat R))},
      Δ ∈ distTriang _ → T Δ.obj₂ → T Δ.obj₃ → T Δ.obj₁)
    (h₂ : ∀ {Δ : Triangle (DerivedCategory (ModuleCat R))},
      Δ ∈ distTriang _ → T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂)
    (h₃ : ∀ {Δ : Triangle (DerivedCategory (ModuleCat R))},
      Δ ∈ distTriang _ → T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃)
    (hR : ∀ k : ℤ, T ((ringSingle R)⟦k⟧)) :
    ∀ M, T M := sorry

/-- The degree-zero regular module is a weak generator of the unbounded derived category. -/
@[stacks 09PB "the regular module is a weak generator"]
theorem ringSingle_isWeakGenerator : IsWeakGenerator (ringSingle R) := sorry

end CategoryTheory.ModuleCat
