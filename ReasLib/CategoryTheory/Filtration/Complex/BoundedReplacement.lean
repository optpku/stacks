module

public import ReasLib.CategoryTheory.Filtration.Complex.BoundedReplacement.Square
public import ReasLib.CategoryTheory.Filtration.Complex.FiniteCategory
public import ReasLib.CategoryTheory.Filtration.Complex.FiniteForget
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded Replacements of Finite Filtered Complexes

@stack 05S5

This file states the intrinsic replacement API for cochain complexes in finite filtered objects.
The hypotheses use the canonical cohomological support predicates on the associated graded
complex, while the conclusions use strict support after forgetting the filtration.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.Finite.CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace Replace

namespace GE

/-- A finite filtered complex whose associated graded complex is cohomologically bounded below
admits a filtered quasi-isomorphic representative that is strictly bounded below after forgetting
the filtration. -/
@[stacks 05S5 "finite filtered bounded-below replacement"]
theorem exists_of_gr (K : FilteredObject.Finite.CochainComplex A) (a : ℤ)
    (hK : ((FilteredObject.Finite.AssociatedGraded.cochain A).obj K).IsGE a) :
    ∃ (L : FilteredObject.Finite.CochainComplex A) (f : K ⟶ L),
      FilteredObject.Finite.CochainComplex.quasiIso A f ∧
        ((FilteredObject.Finite.Forget.cochain A).obj L).IsStrictlyGE a := sorry

end GE

namespace LE

/-- A finite filtered complex whose associated graded complex is cohomologically bounded above
admits a filtered quasi-isomorphic representative that is strictly bounded above after forgetting
the filtration. -/
@[stacks 05S5 "finite filtered bounded-above replacement"]
theorem exists_of_gr (K : FilteredObject.Finite.CochainComplex A) (b : ℤ)
    (hK : ((FilteredObject.Finite.AssociatedGraded.cochain A).obj K).IsLE b) :
    ∃ (M : FilteredObject.Finite.CochainComplex A) (g : M ⟶ K),
      FilteredObject.Finite.CochainComplex.quasiIso A g ∧
        ((FilteredObject.Finite.Forget.cochain A).obj M).IsStrictlyLE b := sorry

end LE

namespace Square

/-- Given lower and upper filtered replacements of a finite filtered complex, lower
cohomological boundedness of its associated graded complex yields a bounded comparison object
and a commutative square of filtered quasi-isomorphisms. -/
@[stacks 05S5 "finite filtered bounded comparison square"]
theorem exists_fill {K L M : FilteredObject.Finite.CochainComplex A} (a b : ℤ)
    (hK : ((FilteredObject.Finite.AssociatedGraded.cochain A).obj K).IsGE a)
    (f : K ⟶ L) (g : M ⟶ K)
    (hf : FilteredObject.Finite.CochainComplex.quasiIso A f)
    (hg : FilteredObject.Finite.CochainComplex.quasiIso A g)
    (hL : ((FilteredObject.Finite.Forget.cochain A).obj L).IsStrictlyGE a)
    (hM : ((FilteredObject.Finite.Forget.cochain A).obj M).IsStrictlyLE b) :
    ∃ (N : FilteredObject.Finite.CochainComplex A) (u : M ⟶ N) (v : N ⟶ L),
      FilteredObject.Finite.CochainComplex.quasiIso A u ∧
        FilteredObject.Finite.CochainComplex.quasiIso A v ∧
        CommSq u g v f ∧
        ((FilteredObject.Finite.Forget.cochain A).obj N).IsStrictlyGE a ∧
        ((FilteredObject.Finite.Forget.cochain A).obj N).IsStrictlyLE b := sorry

end Square

namespace Bounded

/-- If the associated graded complex of a finite filtered complex is cohomologically supported
between `a` and `b`, then lower, upper, and bounded strict representatives fit into a commutative
square of filtered quasi-isomorphisms. -/
@[stacks 05S5 "finite filtered bounded replacement square"]
theorem exists_of_gr (K : FilteredObject.Finite.CochainComplex A) (a b : ℤ)
    (hGE : ((FilteredObject.Finite.AssociatedGraded.cochain A).obj K).IsGE a)
    (hLE : ((FilteredObject.Finite.AssociatedGraded.cochain A).obj K).IsLE b) :
    ∃ (L : FilteredObject.Finite.CochainComplex A) (f : K ⟶ L)
      (M : FilteredObject.Finite.CochainComplex A) (g : M ⟶ K)
      (N : FilteredObject.Finite.CochainComplex A) (u : M ⟶ N) (v : N ⟶ L),
      FilteredObject.Finite.CochainComplex.quasiIso A f ∧
        FilteredObject.Finite.CochainComplex.quasiIso A g ∧
        FilteredObject.Finite.CochainComplex.quasiIso A u ∧
        FilteredObject.Finite.CochainComplex.quasiIso A v ∧
        CommSq u g v f ∧
        ((FilteredObject.Finite.Forget.cochain A).obj L).IsStrictlyGE a ∧
        ((FilteredObject.Finite.Forget.cochain A).obj M).IsStrictlyLE b ∧
        ((FilteredObject.Finite.Forget.cochain A).obj N).IsStrictlyGE a ∧
        ((FilteredObject.Finite.Forget.cochain A).obj N).IsStrictlyLE b := sorry

end Bounded

end Replace

end CategoryTheory.FilteredObject.Finite.CochainComplex
