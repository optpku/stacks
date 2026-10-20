/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.Flat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.QuasiIso
public import ReasLib.Algebra.Homology.HomologicalComplex.MonoEpi
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flat resolutions of ringed-site module complexes

The resolution interface is stated directly with the canonical predicates `IsKFlat` and
`HomologicalComplex.IsTermwiseFlat`.  No chapter-specific property or proof-local instance is part of this owner.
-/

@[expose] public section

open CategoryTheory HomologicalComplex

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]

/-- Lemma 21.17.11 (06YS): every module complex has a termwise-epimorphic quasi-isomorphic
K-flat replacement with termwise-flat source. -/
@[stacks 06YS "termwise-epimorphic K-flat resolution"]
theorem exists_termwiseEpi_quasiIso_from_KFlat_complex_of_flat_terms
    (𝒢 : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ) :
    ∃ (K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ) (α : K ⟶ 𝒢),
      K.IsKFlat ∧
      IsTermwiseFlat K ∧
      QuasiIso α ∧
      ∀ n : ℤ, Epi (α.f n) := sorry

/-- Lemma 21.17.11 (06YS): the same replacement has an epimorphic comparison at complex level. -/
theorem exists_epi_quasiIso_from_KFlat_complex_of_flat_terms
    (𝒢 : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ) :
    ∃ (K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ) (α : K ⟶ 𝒢),
      K.IsKFlat ∧
      IsTermwiseFlat K ∧
      QuasiIso α ∧
      Epi α := sorry

end SheafOfModules.RingedSite
