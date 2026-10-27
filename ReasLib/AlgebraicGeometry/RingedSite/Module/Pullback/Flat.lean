/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of flat modules on ringed sites

Module pullback along an arbitrary morphism of ringed sites preserves flat objects.  It also
preserves a short exact sequence whenever the quotient is flat.  These properties belong to the
canonical `RingedSite.Hom.modulePullback`, rather than to a presentation by a raw continuous
functor and an unbundled structure map.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.IsFlat

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JC AddCommGrpCat.{max u v}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasWeakSheafify JD AddCommGrpCat.{max u v}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪C : Sheaf JC CommRingCat.{max u v}}
variable {𝒪D : Sheaf JD CommRingCat.{max u v}}
variable (f : RingedSite.ofCommRingSheaf JC 𝒪C ⟶ RingedSite.ofCommRingSheaf JD 𝒪D)
variable [(RingedSite.Hom.modulePushforward f).IsRightAdjoint]

/-- Lemma 18.39.1 (05VD): pullback along an arbitrary morphism of ringed sites preserves flat
module sheaves. -/
@[stacks 05VD, stacks 0H97 "ringed-space specialization"]
instance modulePullback (M : ringedSiteModuleCategory JD 𝒪D) [IsFlat 𝒪D M] :
    IsFlat 𝒪C ((RingedSite.Hom.modulePullback f).obj M) := sorry

end SheafOfModules.RingedSite.IsFlat

namespace RingedSite.Hom

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JD AddCommGrpCat.{max u v}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪C : Sheaf JC CommRingCat.{max u v}}
variable {𝒪D : Sheaf JD CommRingCat.{max u v}}
variable (f : RingedSite.ofCommRingSheaf JC 𝒪C ⟶ RingedSite.ofCommRingSheaf JD 𝒪D)
variable [(RingedSite.Hom.modulePushforward f).IsRightAdjoint]

/-- Lemma 18.39.4 (0G6R): module pullback preserves a short exact sequence whose quotient term
is flat. -/
@[stacks 0G6R]
theorem map_shortExact_of_flat_X₃
    (S : ShortComplex (SheafOfModules.RingedSite.ringedSiteModuleCategory JD 𝒪D))
    (hS : S.ShortExact)
    [SheafOfModules.RingedSite.IsFlat 𝒪D S.X₃] :
    (S.map (RingedSite.Hom.modulePullback f)).ShortExact := sorry

end RingedSite.Hom
