/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.Flat
import StacksCheckRecall

/-!
# Flatness across a strict morphism of first-order thickenings of ringed topoi

The inverse-image base ring sheaves `OB` and `OB'` and the source ring sheaves
`O` and `O'` form a commutative square on the source site. For a strict square
and a module whose reduction is flat over `OB`, flatness over `OB'` is equivalent
to invertibility of the canonical comparison. In that case both factors are invertible.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.ChangeOfRings
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {OB' OB O' O : Sheaf J CommRingCat.{max u v}}
variable {π : O' ⟶ O} {τ : OB' ⟶ OB}
variable [IsFirstOrderThickening π] [IsFirstOrderThickening τ]
variable [(restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable (f : OB ⟶ O) [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
variable (f' : OB' ⟶ O') (hcomm : f' ≫ π = τ ≫ f)
variable (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O')
variable [hflat : IsFlat OB ((restrictionAlong f).obj
    ((extendScalars (ringSheafMap π)).obj F'))]

/- Lemma 91.11.2. For a strict morphism of first-order thickenings of ringed topoi,
a module with flat reduction is flat over the thickened base exactly when the
canonical comparison is an isomorphism. The base ring sheaves below are pulled
back to the source site. -/
@[stacks 08MQ] #check (SheafOfModules.RingedSite.FirstOrderThickening.isFlat_iff_canonicalMap_isIso f f' hcomm F' :
  IsStrict f f' hcomm →
    (IsFlat OB' ((restrictionAlong f').obj F') ↔
      IsIso (canonicalMap π f f' hcomm F')))

/- Moreover, both factors of the canonical comparison are isomorphisms in this case. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.canonicalMaps_isIso f f' hcomm F' :
  IsStrict f f' hcomm → IsIso (canonicalMap π f f' hcomm F') →
    IsIso (sourceIdealTensorMap π f f' hcomm F') ∧
      IsIso (idealMulInfMap π F'))

end SheafOfModules.RingedSite.FirstOrderThickening
