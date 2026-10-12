/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.FlatModel
import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-complex view of relative-perfect models

The core criterion uses an explicitly bounded cochain complex.  This leaf gives the equivalent
`Compᵇ` presentation used by the source while keeping the underlying model API in `FlatModel`.

@stack 0DHV
-/

@[expose] public section

noncomputable section

open CategoryTheory ComplexShape
open scoped CategoryTheory

universe u

namespace CategoryTheory.DerivedCategory.IsPerfectOver

variable {A : Type u} [CommRing A]

/-- Lemma 15.84.4 (Stacks `0DHV`): for a flat finitely presented map `R → A`, an object
`K : D(A)` is perfect over `R` if and only if it is isomorphic to a bounded complex of
`R`-flat, finitely presented `A`-modules. -/
@[stacks 0DHV "bounded relative-flat representative criterion"]
theorem iff_exists_bounded_flat_finitePresentation_representative
    (R : Type u) [CommRing R] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat A)) :
    IsPerfectOver R K ↔
      ∃ P : Compᵇ((ModuleCat A)),
        CochainComplex.IsTermwiseFlat
          (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (up ℤ)).obj
            P.obj) ∧
          (∀ i : ℤ, Module.FinitePresentation A (P.obj.X i)) ∧
          IsIsomorphic K (DerivedCategory.Q.obj P.obj) := sorry
/- Proof strategy: translate between `Compᵇ(ModuleCat A)` and an explicitly bounded cochain
complex using the bounded homotopy-category owner, rewrite the termwise conditions through
restriction of scalars, and apply `IsPerfectOver.iff_exists_flat_finitePresentation_model` in both
directions. -/

end CategoryTheory.DerivedCategory.IsPerfectOver
