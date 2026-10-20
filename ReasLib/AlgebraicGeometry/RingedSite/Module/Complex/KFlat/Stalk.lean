/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Stalk
public import ReasLib.CategoryTheory.Sites.Point.Enough
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalkwise detection of K-flat complexes

K-flatness of a complex of modules on a commutative ringed site passes to module-valued stalks.
On a site with enough points, the stalk conditions also detect K-flatness.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite

noncomputable section

universe u v w t

namespace SheafOfModules.RingedSite.CochainComplex

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}}

/-- Lemma 21.18.6 (1): a K-flat complex has K-flat module-stalk complexes. -/
@[stacks 0DEN "(1)"]
theorem IsKFlat.stalk
    {K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ}
    (hK : K.IsKFlat) (p : GrothendieckTopology.Point.{w} J) :
    ((p.moduleStalkComplex O).obj K).IsKFlat := sorry

/-- K-flatness is detected by any conservative indexed family of module-stalk functors. -/
@[stacks 0DEN "conservative family"]
theorem isKFlat_iff_forall_stalk_of_isConservativeFamily
    {I : Type t} (points : I → GrothendieckTopology.Point.{w} J)
    (hpoints : (ofObj points).IsConservativeFamilyOfPoints)
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ) :
    K.IsKFlat ↔ ∀ i : I, (((points i).moduleStalkComplex O).obj K).IsKFlat := sorry

/-- Lemma 21.18.6 (2): on a site with enough points, stalkwise K-flatness implies K-flatness. -/
theorem isKFlat_of_forall_stalk_of_hasEnoughPoints
    [GrothendieckTopology.HasEnoughPoints.{w} J]
    {K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ}
    (hK : ∀ p : GrothendieckTopology.Point.{w} J,
      ((p.moduleStalkComplex O).obj K).IsKFlat) :
    K.IsKFlat := sorry

/-- On a site with enough points, K-flatness is equivalent to K-flatness of all module-stalk
complexes. -/
@[stacks 0DEN "(2)"]
theorem isKFlat_iff_forall_stalk_of_hasEnoughPoints
    [GrothendieckTopology.HasEnoughPoints.{w} J]
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ) :
    K.IsKFlat ↔ ∀ p : GrothendieckTopology.Point.{w} J,
      ((p.moduleStalkComplex O).obj K).IsKFlat := sorry

end SheafOfModules.RingedSite.CochainComplex
