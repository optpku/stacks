/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.CanonicalMap

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

section ReducedFlatness

variable (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O')
variable [hflat : IsFlat OB ((restrictionAlong f).obj
    ((extendScalars (ringSheafMap π)).obj F'))]

include hflat in
/-- For a strict square of first-order thickenings and a module with flat reduction,
flatness over the thickened base is equivalent to invertibility of the canonical comparison. -/
theorem isFlat_iff_canonicalMap_isIso (hstrict : IsStrict f f' hcomm) :
    IsFlat OB' ((restrictionAlong f').obj F') ↔
      IsIso (canonicalMap π f f' hcomm F') := sorry

include hflat in
/-- For a strict square of first-order thickenings and a module with flat reduction,
invertibility of the canonical comparison implies invertibility of both its factors. -/
theorem canonicalMaps_isIso (hstrict : IsStrict f f' hcomm)
    (h : IsIso (canonicalMap π f f' hcomm F')) :
    IsIso (sourceIdealTensorMap π f f' hcomm F') ∧
      IsIso (idealMulInfMap π F') := sorry

end ReducedFlatness

variable (G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O')
variable [hflatThickened : IsFlat OB' ((restrictionAlong f').obj G')]

include hflatThickened in
/-- For a strict square of first-order thickenings, flatness of a module over the
thickened base makes the comparison from the pulled-back base ideal tensored with
its reduction to its ideal multiple an isomorphism. -/
theorem canonicalMap_isIso_of_isFlat (hstrict : IsStrict f f' hcomm) :
    IsIso (canonicalMap π f f' hcomm G') := sorry

include hflatThickened in
/-- The canonical comparison for a module flat over the thickened base is invertible
when the pulled-back base ideal maps epimorphically to the source ideal. -/
instance instIsIso_canonicalMap_of_isFlat
    [hstrict : Epi (kernelPullbackMap f f' hcomm)] :
    IsIso (canonicalMap π f f' hcomm G') :=
  canonicalMap_isIso_of_isFlat f f' hcomm G' hstrict

end SheafOfModules.RingedSite.FirstOrderThickening
