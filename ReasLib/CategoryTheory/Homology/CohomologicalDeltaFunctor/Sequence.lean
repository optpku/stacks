module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Exact Windows of Cohomological Delta Functors

This leaf names the six objects and five arrows around one connecting map in
the long exact sequence of a cohomological delta functor. It also packages the
map of windows induced by a morphism of delta functors.
-/

open CategoryTheory.ComposableArrows

universe vA uA vB uB

namespace CategoryTheory.CohomologicalDeltaFunctor

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]

/-- The six-object, five-arrow window around the degree-`n` connecting map
associated to a short exact sequence. -/
@[stacks 010Q "exact window of a cohomological delta functor"]
def exactWindow (F : CohomologicalDeltaFunctor A B)
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    ComposableArrows B 5 :=
  mk₅ ((F.F n).obj.map S.f) ((F.F n).obj.map S.g) (F.δ hS n)
    ((F.F (n + 1)).obj.map S.f) ((F.F (n + 1)).obj.map S.g)

/-- The canonical window of a cohomological delta functor is exact. -/
@[stacks 010Q "exactness of a cohomological delta-functor window"]
theorem exactWindow_exact (F : CohomologicalDeltaFunctor A B)
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (F.exactWindow hS n).Exact := sorry

/-- A morphism of cohomological delta functors induces a morphism between
their exact windows. -/
@[stacks 010R "map of cohomological delta-functor exact windows"]
def exactWindowMap {F G : CohomologicalDeltaFunctor A B} (τ : Hom F G)
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    F.exactWindow hS n ⟶ G.exactWindow hS n :=
  ComposableArrows.homMk₅
    ((τ.app n).app S.X₁) ((τ.app n).app S.X₂) ((τ.app n).app S.X₃)
    ((τ.app (n + 1)).app S.X₁) ((τ.app (n + 1)).app S.X₂)
    ((τ.app (n + 1)).app S.X₃)
    ((τ.app n).naturality S.f) ((τ.app n).naturality S.g)
    (τ.comm hS n).w.symm
    ((τ.app (n + 1)).naturality S.f) ((τ.app (n + 1)).naturality S.g)

/-- The identity morphism of cohomological delta functors induces the identity
map of exact windows. -/
@[simp]
theorem exactWindowMap_id (F : CohomologicalDeltaFunctor A B)
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    exactWindowMap (Hom.id F) hS n = 𝟙 (F.exactWindow hS n) := sorry

/-- Maps of exact windows preserve composition of cohomological
delta-functor morphisms. -/
@[simp]
theorem exactWindowMap_comp
    {F G H : CohomologicalDeltaFunctor A B} (τ : Hom F G) (σ : Hom G H)
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    exactWindowMap (Hom.comp τ σ) hS n =
      exactWindowMap τ hS n ≫ exactWindowMap σ hS n := sorry

/-- The first nonnegative-degree exact window of a cohomological delta
functor. -/
@[stacks 010Q "low-degree window of a cohomological delta functor"]
abbrev lowDegreeWindow (F : CohomologicalDeltaFunctor A B)
    {S : ShortComplex A} (hS : S.ShortExact) : ComposableArrows B 5 :=
  F.exactWindow hS 0

/-- The low-degree window of a cohomological delta functor is exact. -/
@[stacks 010Q "exactness of the low-degree delta-functor window"]
theorem lowDegreeWindow_exact (F : CohomologicalDeltaFunctor A B)
    {S : ShortComplex A} (hS : S.ShortExact) :
    (F.lowDegreeWindow hS).Exact := sorry

/-- A morphism of cohomological delta functors induces a map of low-degree
exact windows. -/
@[stacks 010R "map of low-degree delta-functor windows"]
abbrev lowDegreeWindowMap {F G : CohomologicalDeltaFunctor A B} (τ : Hom F G)
    {S : ShortComplex A} (hS : S.ShortExact) :
    F.lowDegreeWindow hS ⟶ G.lowDegreeWindow hS :=
  exactWindowMap τ hS 0

end CategoryTheory.CohomologicalDeltaFunctor
