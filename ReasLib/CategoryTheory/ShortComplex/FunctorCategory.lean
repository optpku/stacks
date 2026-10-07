module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pointwise exactness for short complexes

This neutral owner evaluates a short complex in a functor category at an arbitrary object of its
index category.  The exactness API is independent of whether the index is a filtered order,
`ℕᵒᵖ`, or another diagram shape.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe vJ uJ vC uC

namespace CategoryTheory.ShortComplex.FunctorCategory

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]

/- The stagewise short complex is the canonical evaluation of a functor-category object. -/
/-- Evaluate a short complex of `J`-diagrams at an object of `J`. -/
abbrev app [HasZeroMorphisms C] (S : ShortComplex (J ⥤ C)) (j : J) : ShortComplex C :=
  S.map ((evaluation J C).obj j)

/-- A chosen splitting after every evaluation of a functor-category short complex.  No
naturality of the chosen splittings is asserted. -/
@[stacks 0192 "pointwise splitting of a functor-category short complex"]
abbrev PointwiseSplitting [Preadditive C] (S : ShortComplex (J ⥤ C)) :=
  ∀ j : J, (app S j).Splitting

section Abelian

variable [Abelian C]

/- Exactness in a functor category is detected pointwise. -/
/-- Exactness of a functor-category short complex is equivalent to stagewise exactness. -/
@[stacks 02MZ]
theorem exact_iff_exact_app (S : ShortComplex (J ⥤ C)) :
    S.Exact ↔ ∀ j : J, (app S j).Exact := sorry

/-- Short exactness of a functor-category short complex is equivalent to short exactness after
every evaluation. -/
@[stacks 0192 "pointwise criterion for a short exact functor-category complex"]
theorem shortExact_iff_shortExact_app (S : ShortComplex (J ⥤ C)) :
    S.ShortExact ↔ ∀ j : J, (app S j).ShortExact := sorry

namespace ShortExact

/-- A short exact functor-category row remains short exact after evaluation. -/
theorem app {S : ShortComplex (J ⥤ C)} {j : J} (hS : S.ShortExact) :
    (FunctorCategory.app S j).ShortExact := sorry

end ShortExact

end Abelian

namespace PointwiseSplitting

/-- A pointwise splitting makes every evaluated short complex short exact. -/
theorem shortExactApp [Preadditive C] [HasZeroObject C]
    {S : ShortComplex (J ⥤ C)} (σ : PointwiseSplitting S) (j : J) :
    (app S j).ShortExact := sorry

/-- A pointwise split short complex in a functor category over an abelian category is short
exact. -/
theorem shortExact [Abelian C] {S : ShortComplex (J ⥤ C)}
    (σ : PointwiseSplitting S) : S.ShortExact := sorry

end PointwiseSplitting

end CategoryTheory.ShortComplex.FunctorCategory
