/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import ReasLib.CategoryTheory.DerivedCategory.Limit.RightDerived
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Sites.Cohomology.Derived

/-!
# Sheaf Cohomology of the Chaotic Natural-Number Site

This leaf owns the narrow bridge used for the textbook observation that a sequential inverse
limit is global sections on the chaotic site of `ℕ`.  The site-generic derived comparison lives
in `Sites/Cohomology/Derived`; this file only supplies the canonical bottom-topology equivalence
and its sequential specialization.
@stack 091A
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CategoryTheory.DerivedLimit.NaturalNumbersSite

namespace GlobalSections

#synth IsGrothendieckAbelian (SequentialInverseSystem AddCommGrpCat)
#synth EnoughInjectives (SequentialInverseSystem AddCommGrpCat)
#synth HasInjectiveResolutions (SequentialInverseSystem AddCommGrpCat)
#synth IsGrothendieckAbelian (Sheaf (⊥ : GrothendieckTopology ℕ) AddCommGrpCat)
#synth HasExt (Sheaf (⊥ : GrothendieckTopology ℕ) AddCommGrpCat)

/-- Remark 15.87.8 (1) (091A): on the chaotic site of `ℕ`, global sections of the sheaf
corresponding to a sequential inverse system are canonically its inverse limit. -/
@[stacks 091A]
noncomputable def isoLimit :
    (sheafBotEquivalence AddCommGrpCat).inverse ⋙
        Sheaf.Γ (⊥ : GrothendieckTopology ℕ) AddCommGrpCat ≅
      (lim : SequentialInverseSystem AddCommGrpCat ⥤ AddCommGrpCat) :=
  Functor.isoWhiskerLeft
      ((sheafBotEquivalence AddCommGrpCat).inverse)
      (Sheaf.ΓNatIsoLim (⊥ : GrothendieckTopology ℕ) AddCommGrpCat) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sheafBotEquivalence AddCommGrpCat).counitIso _ ≪≫
    Functor.leftUnitor _

end GlobalSections

namespace Comparison

/-- Remark 15.87.8 (2) (091A): the right-derived inverse-limit functor on sequential abelian
groups agrees with the sheaf cohomology functor of the associated sheaf on the chaotic site of
`ℕ`. -/
@[stacks 091A]
theorem rightDerived_iso_cohomology (p : ℕ) :
    IsIsomorphic
      (DerivedLimit.rightDerived (A := AddCommGrpCat) p)
      ((sheafBotEquivalence AddCommGrpCat).inverse ⋙
        Sheaf.functorH (⊥ : GrothendieckTopology ℕ) p) := sorry

/-- Objectwise form of the derived-limit/cohomology comparison. -/
theorem rightDerived_obj_iso_cohomology
    (A : SequentialInverseSystem AddCommGrpCat) (p : ℕ) :
    IsIsomorphic
      ((DerivedLimit.rightDerived (A := AddCommGrpCat) p).obj A)
      ((Sheaf.functorH (⊥ : GrothendieckTopology ℕ) p).obj
        ((sheafBotEquivalence AddCommGrpCat).inverse.obj A)) := sorry

end Comparison

end CategoryTheory.DerivedLimit.NaturalNumbersSite
