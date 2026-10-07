module

public import stacks_project.Chap91.Lemma_91_11_1_Lift
public import stacks_project.Chap91.Lemma_91_11_6_Obstruction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Obstruction to lifting a map of modules along a strict morphism of first-order thickenings

Along a strict morphism of first-order thickenings as in Situation 91.9.1, an `O`-linear
map `φ : i^* F' ⟶ i^* G'` between modules flat over `O_{B'}` lifts to an `O'`-linear map
`F' ⟶ G'` if and only if the canonical class `obstruction π f f' hcomm hstrict φ` in
`Ext (i^* F') (f^* J ⊗ i^* G') 1` vanishes.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian (Ext)
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
variable (F' G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O')
variable (φ : (extendScalars (ringSheafMap π)).obj F' ⟶
    (extendScalars (ringSheafMap π)).obj G')
variable [IsFlat OB' ((restrictionAlong f').obj F')]
variable [IsFlat OB' ((restrictionAlong f').obj G')]
variable [HasExt (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]

/-- Lemma 91.11.6: Let `(f, f')` be a morphism of first-order thickenings as in
Situation 91.9.1. Let `F'`, `G'` be `O'`-modules and set `F = i^* F'` and
`G = i^* G'`. Let `φ : F ⟶ G` be an `O`-linear map. Assume that `F'` and `G'`
are flat over `O_{B'}` and that `(f, f')` is a strict morphism of thickenings.
There is a canonical class `obstruction π f f' hcomm hstrict φ` in
`Ext (i^* F') (f^* J ⊗ i^* G') 1` (the source writes `Ext^1_O(F, G ⊗_O f^* J)`)
whose vanishing is necessary and sufficient for the existence of a lift of `φ`
to an `O'`-linear map `φ' : F' ⟶ G'`. -/
@[stacks 08MT]
theorem obstruction_eq_zero_iff (hstrict : IsStrict f f' hcomm) :
    obstruction π f f' hcomm hstrict φ = 0 ↔ Nonempty (Lift F' G' φ) := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
