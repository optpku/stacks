/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.SemiFree
public import ReasLib.Algebra.Homology.DerivedCategory.KProjective
public import ReasLib.Algebra.Homology.HomotopyCategory.KProjective.Characterization
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# K-Projective Consequences of Semi-Free Filtrations

This leaf records the homotopical consequences of a semi-free filtration,
without imposing a chosen resolution on consumers.
-/

open CategoryTheory
open ComplexShape
open HomotopyCategory

noncomputable section

universe u

namespace CochainComplex

variable {A : Type u} [Ring A]

namespace HasSemiFreeFiltration

/-- Lemma 22.20.2 (09KM): every map from a semi-free differential graded `A`-module to an
acyclic one vanishes in the homotopy category. -/
@[stacks 09KM]
theorem hom_eq_zero_of_acyclic
    {P : ModuleCat.DGMod A} (hP : HasSemiFreeFiltration P)
    {N : ModuleCat.DGMod A} (hN : N.Acyclic)
    (f : (HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj P ⟶
      (HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj N) :
    f = 0 := sorry

/-- A differential graded module with a semi-free filtration is K-projective. -/
@[stacks 09KM "semi-free complexes are K-projective"]
theorem isKProjective {P : ModuleCat.DGMod A} (hP : HasSemiFreeFiltration P) :
    P.IsKProjective := sorry

/-- Stacks 0BYW: for a semi-free source, the canonical localization from the homotopy category
to any chosen derived-category model is bijective on outgoing morphisms. -/
@[stacks 0BYW "semi-free homotopy-to-derived comparison"]
theorem Qh_map_bijective [HasDerivedCategory (ModuleCat A)]
    {P : ModuleCat.DGMod A} (hP : HasSemiFreeFiltration P)
    (N : HomotopyCategory (ModuleCat A) (up ℤ)) :
    Function.Bijective
      (DerivedCategory.Qh.map :
        ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj P ⟶ N) → _) := sorry

/-- Every map from a semi-free differential graded module to an acyclic one is homotopic to
zero. -/
theorem homotopic_to_zero_of_acyclic
    {P N : ModuleCat.DGMod A} (hP : HasSemiFreeFiltration P) (hN : N.Acyclic) (f : P ⟶ N) :
    Nonempty (Homotopy f 0) := sorry

end HasSemiFreeFiltration

end CochainComplex
