module

public import ReasLib.Algebra.Homology.DerivedCategory.ProjectiveAmplitude
public import ReasLib.CategoryTheory.Pretriangulated.Triangle.Split
import Mathlib.Tactic.CrossRefAttribute

/-!
# Splitting from projective amplitude

@stack 0BCG

Projective amplitude gives the expected vanishing against an upper-truncated target.  Applied to
the connecting morphism of a distinguished triangle, this yields a compatible biproduct
splitting; one more degree of vanishing makes that splitting unique.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe u

namespace CategoryTheory

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/-- Lemma 15.77.1 (1) (0BCG): a projective-amplitude object has no morphisms to a derived
object whose homology vanishes at and above the lower amplitude bound. -/
@[stacks 0BCG "(1), projective-amplitude Hom vanishing"]
theorem hom_eq_zero_of_projectiveAmplitude_of_homology_vanishing_ge
    {K L : DMod} {a b : ℤ}
    (hL : HasProjectiveAmplitudeIn L a b)
    (hK : ∀ i : ℤ, a ≤ i → IsZero ((H i).obj K))
    (f : L ⟶ K) :
    f = 0 := sorry

/-- Lemma 15.77.1 (2) (0BCG): under the shifted homology-vanishing bound, a distinguished
triangle with projective-amplitude third vertex admits a compatible biproduct splitting. -/
@[stacks 0BCG "(2), distinguished-triangle splitting"]
theorem exists_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge_succ
    {K L M : DMod} {a b : ℤ}
    (hL : HasProjectiveAmplitudeIn L a b)
    (hK : ∀ i : ℤ, a + 1 ≤ i → IsZero ((H i).obj K))
    {f : K ⟶ M} {g : M ⟶ L} {δ : L ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang DMod) :
    ∃ e : M ≅ K ⊞ L, f ≫ e.hom = biprod.inl ∧ e.hom ≫ biprod.snd = g := sorry

/-- Lemma 15.77.1 (3) (0BCG): with homology vanishing from the lower amplitude bound onward,
the compatible biproduct splitting of the distinguished triangle exists uniquely. -/
@[stacks 0BCG "(3), unique distinguished-triangle splitting"]
theorem existsUnique_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge
    {K L M : DMod} {a b : ℤ}
    (hL : HasProjectiveAmplitudeIn L a b)
    (hK : ∀ i : ℤ, a ≤ i → IsZero ((H i).obj K))
    {f : K ⟶ M} {g : M ⟶ L} {δ : L ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang DMod) :
    ∃! e : M ≅ K ⊞ L, f ≫ e.hom = biprod.inl ∧ e.hom ≫ biprod.snd = g := sorry

end CategoryTheory
