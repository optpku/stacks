/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Stalk
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness of module sheaves at points

The pointwise predicate in this file is ordinary module flatness of the module-valued stalk.
This is preferable to encoding stalkwise flatness indirectly as exactness after forgetting the
stalk module to an additive group.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})
variable (p : GrothendieckTopology.Point.{max u v} J)
variable (M : ringedSiteModuleCategory J 𝒪)

/-- A module sheaf is flat at `p` when its module-valued stalk is flat over the stalk ring. -/
@[stacks 05VB "pointwise flatness"]
abbrev IsFlatAt : Prop :=
  Module.Flat (p.stalkCommRing 𝒪) (p.moduleStalk 𝒪 M)

/-- Lemma 18.39.2 (05VB): a flat module sheaf has a flat module-valued stalk at every point. -/
@[stacks 05VB]
instance IsFlat.atPoint [IsFlat 𝒪 M] : IsFlatAt 𝒪 p M := sorry

section ConservativeFamily

variable {I : Type w} (points : I → GrothendieckTopology.Point.{max u v} J)

/-- Lemma 18.39.3 (05VC): flatness of a module sheaf is detected by any conservative family of
module-valued stalk functors. -/
@[stacks 05VC]
theorem isFlat_iff_forall_isFlatAt
    (hpoints : (ofObj points).IsConservativeFamilyOfPoints) :
    IsFlat 𝒪 M ↔ ∀ i : I, IsFlatAt 𝒪 (points i) M := sorry

/-- Construct flatness of a module sheaf from flatness at every point of a conservative family. -/
theorem IsFlat.of_forall_isFlatAt
    (hpoints : (ofObj points).IsConservativeFamilyOfPoints)
    (hM : ∀ i : I, IsFlatAt 𝒪 (points i) M) :
    IsFlat 𝒪 M := sorry

end ConservativeFamily

end SheafOfModules.RingedSite
