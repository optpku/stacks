/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import stacks_project.Chap103.Lemma_103_14_4_LowerShriek
public import stacks_project.Chap103.Lemma_103_16_1

/-!
# Quasi-coherence of module lower shriek

On an algebraic stack, module lower shriek along the lisse-étale and
flat-fppf inclusions preserves quasi-coherence.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Ring-to-abelian-group sheaf composition exists on every slice of the
lisse-étale topology of an algebraic stack. -/
instance lisseEtaleTopology_over_hasSheafCompose
    (X : GroupoidsOver S) [AlgebraicStack X] :
    ∀ x, ((lisseEtaleTopology X).over x).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Weak sheafification of abelian groups exists on every slice of the
lisse-étale topology of an algebraic stack. -/
instance lisseEtaleTopology_over_hasWeakSheafify
    (X : GroupoidsOver S) [AlgebraicStack X] :
    ∀ x, HasWeakSheafify ((lisseEtaleTopology X).over x) AddCommGrpCat.{u} :=
  sorry

/-- On every slice of the lisse-étale topology of an algebraic stack,
sheafification equivalences are the locally bijective morphisms. -/
instance lisseEtaleTopology_over_wEqualsLocallyBijective
    (X : GroupoidsOver S) [AlgebraicStack X] :
    ∀ x, ((lisseEtaleTopology X).over x).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

/-- Ring-to-abelian-group sheaf composition exists on every slice of the
flat-fppf topology of an algebraic stack. -/
instance flatFppfTopology_over_hasSheafCompose
    (X : GroupoidsOver S) [AlgebraicStack X] :
    ∀ x, ((flatFppfTopology X).over x).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Weak sheafification of abelian groups exists on every slice of the
flat-fppf topology of an algebraic stack. -/
instance flatFppfTopology_over_hasWeakSheafify
    (X : GroupoidsOver S) [AlgebraicStack X] :
    ∀ x, HasWeakSheafify ((flatFppfTopology X).over x) AddCommGrpCat.{u} :=
  sorry

/-- On every slice of the flat-fppf topology of an algebraic stack,
sheafification equivalences are the locally bijective morphisms. -/
instance flatFppfTopology_over_wEqualsLocallyBijective
    (X : GroupoidsOver S) [AlgebraicStack X] :
    ∀ x, ((flatFppfTopology X).over x).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

variable {X : GroupoidsOver S} [AlgebraicStack X]

namespace lisseEtaleModuleLowerShriek

/-- Lemma 103.16.2 (1): let `X` be an algebraic stack. If `H` is a quasi-coherent
`𝒪_{X_lisse,étale}`-module on the lisse-étale site of `X`, then
`(lisseEtaleModuleLowerShriek X).obj H` is a quasi-coherent module on the
étale site of `X`. -/
@[stacks 07B0]
instance obj_isQuasicoherent
    (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X))
    [H.IsQuasicoherent] :
    ((lisseEtaleModuleLowerShriek X).obj H).IsQuasicoherent :=
  sorry

end lisseEtaleModuleLowerShriek

namespace flatFppfModuleLowerShriek

/-- Lemma 103.16.2 (2): let `X` be an algebraic stack. If `H` is a quasi-coherent
`𝒪_{X_flat,fppf}`-module on the flat-fppf site of `X`, then
`(flatFppfModuleLowerShriek X).obj H` is a quasi-coherent module on the fppf
site of `X`. -/
@[stacks 07B0]
instance obj_isQuasicoherent
    (H : SheafOfModules.{u} (flatFppfStructureSheaf X))
    [H.IsQuasicoherent] :
    ((flatFppfModuleLowerShriek X).obj H).IsQuasicoherent :=
  sorry

end flatFppfModuleLowerShriek

end AlgebraicGeometry.AlgebraicStack
