module

public import stacks_project.Chap91.Lemma_91_11_2_Canonical
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness across a strict morphism of first-order thickenings of ringed topoi

After identifying underlying topoi, a strict morphism of first-order thickenings as in
Situation 91.9.1 / Definition 91.9.2 is a commutative square of ring sheaves with
epimorphic `kernelPullbackMap`. For an `O'`-module `F'` with `F = i^* F'` flat over
`O_B`, flatness of `F'` over `O_{B'}` is equivalent to invertibility of `canonicalMap`.
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
variable [IsFlat OB ((restrictionAlong f).obj
    ((extendScalars (ringSheafMap π)).obj F'))]

/-- Lemma 91.11.2 (1): Let `(f, f')` be a morphism of first-order thickenings of
ringed topoi as in Situation 91.9.1. Let `F'` be an `O'`-module and set
`F = i^* F'`. Assume that `F` is flat over `O_B` and that `(f, f')` is a
strict morphism of thickenings (Definition 91.9.2). Then `F'` is flat over
`O_{B'}` if and only if the canonical map `f^* J ⊗_O F ⟶ I F'` is an
isomorphism. -/
@[stacks 08MQ]
theorem isFlat_iff_canonicalMap_isIso (hstrict : IsStrict f f' hcomm) :
    IsFlat OB' ((restrictionAlong f').obj F') ↔
      IsIso (canonicalMap π f f' hcomm F') := sorry

/-- Lemma 91.11.2 (2): Moreover, in this case the maps
`f^* J ⊗_O F ⟶ I ⊗_O F ⟶ I F'` are isomorphisms. -/
@[stacks 08MQ]
theorem canonicalMaps_isIso (hstrict : IsStrict f f' hcomm)
    (h : IsIso (canonicalMap π f f' hcomm F')) :
    IsIso (sourceIdealTensorMap π f f' hcomm F') ∧
      IsIso (idealMulInfMap π F') := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
