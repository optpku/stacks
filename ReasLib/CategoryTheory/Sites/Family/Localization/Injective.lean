/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.Family.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Injectivity under family localization

Localization inverse image at a semi-representable family preserves injective
abelian sheaves and K-injective cochain complexes of abelian sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

universe w u v

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

/-- Inverse image along localization at a semi-representable family preserves
injective abelian sheaves. -/
@[stacks 0D88, instance]
instance forget_preservesInjectiveObjects (J : GrothendieckTopology C)
    (K : FormalCoproduct.{w} C) :
    ((forget K).sheafPushforwardContinuous AddCommGrpCat.{max w u v}
      (overTopology J K) J).PreservesInjectiveObjects :=
  sorry

/-- Inverse image along localization at a semi-representable family preserves
K-injective cochain complexes of abelian sheaves. -/
@[stacks 0D88, instance]
instance forget_isKInjective (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C)
    [HasSheafify J AddCommGrpCat.{max w u v}]
    [HasSheafify (overTopology J K) AddCommGrpCat.{max w u v}]
    (I : CochainComplex (Sheaf J AddCommGrpCat.{max w u v}) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      ((((forget K).sheafPushforwardContinuous AddCommGrpCat.{max w u v}
          (overTopology J K) J).mapHomologicalComplex (up ℤ)).obj I) :=
  sorry

end CategoryTheory.SemiRepresentableFamily
