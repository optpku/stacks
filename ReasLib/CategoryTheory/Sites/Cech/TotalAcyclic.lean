/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.Coefficients
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import ReasLib.Algebra.Homology.HomologicalComplex.Acyclic.Homology
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Total acyclicity and extended Cech complexes

This leaf owns the criterion relating positive objectwise cohomology to exactness of the
represented degree-zero extended Cech complex.  The complex itself is supplied by the generic
site Cech coefficient API; no chapter proof-route construction is imported here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v})]

namespace IsTotallyAcyclic

/-- Lemma 21.13.5 (07A1): total acyclicity is equivalent to positive objectwise cohomology
vanishing together with exactness of the extended Cech complex on represented degree-zero
sections for every locally surjective arrow of sheaves of sets. -/
@[stacks 07A1 "total acyclicity and extended Cech exactness"]
theorem iff_objectwise_and_cech
    (F : Sheaf J AddCommGrpCat.{max u v}) :
    IsTotallyAcyclic F ↔
      (∀ (U : C) {p : ℕ}, 0 < p → IsZero (F.H' p U)) ∧
      ∀ ⦃K K' : Sheaf J (Type (max u v))⦄ (α : K' ⟶ K)
        [Sheaf.IsLocallySurjective α],
        (Sheaf.Cech.extended α F).Acyclic := sorry

end IsTotallyAcyclic

end CategoryTheory.Sheaf
