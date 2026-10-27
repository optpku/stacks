/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap106.Lemma_106_12_2_Invariant
public import stacks_project.Chap106.Definition_106_12_1_Moduli
public import stacks_project.Chap97.Theorem_97_17_2

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.SmallModuli
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/- Lemma 106.12.3 (1): Categorical moduli spaces and invariant categorical quotients. -/
@[stacks 0DUI] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.isCategoricalModuliSpace_iff_isCategoricalQuotient :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    {Y : AlgebraicSpace S} (f : (SmallQuotient.quotientStack G) ⟶ Y.toGroupoids),
    -- Local instance justification (defeq pin): the algebraic-stack moduli predicate is indexed by the proved algebraicity of this concrete quotient; the explicit groupoid cannot have a companion instance.
    letI : AlgebraicStack (SmallQuotient.quotientStack G) :=
      isAlgebraicStack_quotientStack_of_flat G inferInstance inferInstance
    AlgebraicStack.IsCategoricalModuliSpace f ↔
      G.IsInvariantHom (G.atlasComp f) ∧
        ∀ {W : AlgebraicSpace S} (ψ : G.U.left ⟶ W),
          G.IsInvariantHom ψ → ∃! χ : Y ⟶ W, G.atlasComp f ≫ χ = ψ)

/- Lemma 106.12.3 (2): Uniform categorical moduli spaces and flat base changes of invariant categorical quotients. -/
@[stacks 0DUI] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.isUniformCategoricalModuliSpace_iff_isUniformCategoricalQuotient :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    {Y : AlgebraicSpace S} (f : (SmallQuotient.quotientStack G) ⟶ Y.toGroupoids),
    -- Local instance justification (defeq pin): the algebraic-stack moduli predicate is indexed by the proved algebraicity of this concrete quotient; the explicit groupoid cannot have a companion instance.
    letI : AlgebraicStack (SmallQuotient.quotientStack G) :=
      isAlgebraicStack_quotientStack_of_flat G inferInstance inferInstance
    AlgebraicStack.IsUniformCategoricalModuliSpace f ↔
      G.IsInvariantHom (G.atlasComp f) ∧
        ∀ {Y' : AlgebraicSpace S} (h : Y' ⟶ Y) [AlgebraicSpace.Flat h]
          {W : AlgebraicSpace S} (ψ : CategoryTheory.Limits.pullback (G.atlasComp f) h ⟶ W)
          (hφ : G.IsInvariantHom (G.atlasComp f)),
          G.baseChangeTgt (G.atlasComp f) hφ h ≫ ψ =
              G.baseChangeSrc (G.atlasComp f) h ≫ ψ →
            ∃! χ : Y' ⟶ W, CategoryTheory.Limits.pullback.snd (G.atlasComp f) h ≫ χ = ψ)

/- Lemma 106.12.3 (3): Categorical moduli spaces in a full subcategory and invariant categorical quotients. -/
@[stacks 0DUI] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.isCategoricalModuliSpaceIn_iff_isCategoricalQuotientIn :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    {Y : AlgebraicSpace S} (f : (SmallQuotient.quotientStack G) ⟶ Y.toGroupoids)
    (C : ObjectProperty (AlgebraicSpace S)),
    -- Local instance justification (defeq pin): the algebraic-stack moduli predicate is indexed by the proved algebraicity of this concrete quotient; the explicit groupoid cannot have a companion instance.
    letI : AlgebraicStack (SmallQuotient.quotientStack G) :=
      isAlgebraicStack_quotientStack_of_flat G inferInstance inferInstance
    AlgebraicStack.IsCategoricalModuliSpaceIn C f ↔
      C Y ∧ G.IsInvariantHom (G.atlasComp f) ∧
        ∀ {W : AlgebraicSpace S} (hW : C W) (ψ : G.U.left ⟶ W),
          G.IsInvariantHom ψ → ∃! χ : Y ⟶ W, G.atlasComp f ≫ χ = ψ)

/- Lemma 106.12.3 (4): Uniform categorical moduli spaces in a full subcategory and invariant categorical quotients. -/
@[stacks 0DUI] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.isUniformCategoricalModuliSpaceIn_iff_isUniformCategoricalQuotientIn :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    {Y : AlgebraicSpace S} (f : (SmallQuotient.quotientStack G) ⟶ Y.toGroupoids)
    (C : ObjectProperty (AlgebraicSpace S)),
    -- Local instance justification (defeq pin): the algebraic-stack moduli predicate is indexed by the proved algebraicity of this concrete quotient; the explicit groupoid cannot have a companion instance.
    letI : AlgebraicStack (SmallQuotient.quotientStack G) :=
      isAlgebraicStack_quotientStack_of_flat G inferInstance inferInstance
    AlgebraicStack.IsUniformCategoricalModuliSpaceIn C f ↔
      C Y ∧ G.IsInvariantHom (G.atlasComp f) ∧
        ∀ {Y' : AlgebraicSpace S} (h : Y' ⟶ Y) (hY' : C Y')
          [AlgebraicSpace.Flat h] {W : AlgebraicSpace S} (hW : C W)
          (ψ : CategoryTheory.Limits.pullback (G.atlasComp f) h ⟶ W)
          (hφ : G.IsInvariantHom (G.atlasComp f)),
          G.baseChangeTgt (G.atlasComp f) hφ h ≫ ψ =
              G.baseChangeSrc (G.atlasComp f) h ≫ ψ →
            ∃! χ : Y' ⟶ W, CategoryTheory.Limits.pullback.snd (G.atlasComp f) h ≫ χ = ψ)

end AlgebraicGeometry.GroupoidAlgebraicSpace
