/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import stacks_project.Chap96.Lemma_96_21_2_HigherDirectImage
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact

/-!
# Lemma 103.13.2

Filtered colimits of abelian sheaves commute with higher direct images along a
quasi-compact quasi-separated morphism of algebraic stacks, both in the fppf
topology and in the étale topology.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicStack GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 103.13.2 (1): Let `f : X ⟶ Y` be a quasi-compact and quasi-separated
morphism of algebraic stacks. If `ℱ` is a filtered diagram of abelian sheaves
on `X` in the fppf topology, then for every `p : ℕ` the canonical map
`colimit.post ℱ (higherDirectImageFunctor f StandardTopology.fppf p)` is an
isomorphism. -/
@[stacks 0GQW]
instance higherDirectImageFunctor_fppf_colimitComparison_isIso
    {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [AlgebraicStack X] [AlgebraicStack Y] [QuasiCompact f] [QuasiSeparated f]
    [HasSheafify X.fppfTopology AddCommGrpCat.{u + 1}]
    [HasSheafify Y.fppfTopology AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf X.fppfTopology AddCommGrpCat.{u + 1})]
    {I : Type (u + 1)} [Category.{u + 1} I] [IsFiltered I]
    (ℱ : I ⥤ Sheaf X.fppfTopology AddCommGrpCat.{u + 1})
    [HasColimit ℱ] (p : ℕ)
    [HasColimit (ℱ ⋙ higherDirectImageFunctor f StandardTopology.fppf p)] :
    IsIso (colimit.post ℱ (higherDirectImageFunctor f StandardTopology.fppf p)) :=
  sorry

/-- Lemma 103.13.2 (2): Let `f : X ⟶ Y` be a quasi-compact and quasi-separated
morphism of algebraic stacks. If `ℱ` is a filtered diagram of abelian sheaves
on `X_étale`, then for every `p : ℕ` the canonical map
`colimit.post ℱ (higherDirectImageFunctor f StandardTopology.etale p)` is an
isomorphism. -/
@[stacks 0GQW]
instance higherDirectImageFunctor_etale_colimitComparison_isIso
    {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [AlgebraicStack X] [AlgebraicStack Y] [QuasiCompact f] [QuasiSeparated f]
    [HasSheafify X.etaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify Y.etaleTopology AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf X.etaleTopology AddCommGrpCat.{u + 1})]
    {I : Type (u + 1)} [Category.{u + 1} I] [IsFiltered I]
    (ℱ : I ⥤ Sheaf X.etaleTopology AddCommGrpCat.{u + 1})
    [HasColimit ℱ] (p : ℕ)
    [HasColimit (ℱ ⋙ higherDirectImageFunctor f StandardTopology.etale p)] :
    IsIso (colimit.post ℱ (higherDirectImageFunctor f StandardTopology.etale p)) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
