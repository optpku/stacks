module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap71.Lemma_71_2_3_WeaklyAssociated

/-!
# Lemma 71.2.5

A quasi-coherent module on an algebraic space is zero if and only if its
weakly associated locus is empty.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Lemma 71.2.5: for a scheme `S`, an algebraic space `X` over `S`, and a
quasi-coherent `𝒪_X`-module `F`, `F` is the zero module if and only if its
weakly associated locus is empty. -/
@[stacks 0CU0]
theorem isZero_iff_weakAss_eq_empty (F : X.Modules) [F.IsQuasicoherent] :
    IsZero F ↔ F.weakAss = (∅ : Set (Points X)) :=
  sorry

/-- A quasi-coherent module on an algebraic space is zero if and only if no
point is weakly associated to it. -/
theorem isZero_iff_forall_not_weaklyAssociatedAt (F : X.Modules)
    [F.IsQuasicoherent] :
    IsZero F ↔ ∀ x : Points X, ¬ F.weaklyAssociatedAt x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
