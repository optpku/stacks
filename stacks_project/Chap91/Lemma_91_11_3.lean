/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Situation_91_12_2_Diagram
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite presentation across a strict morphism of first-order thickenings

After identifying underlying topoi, a strict morphism of first-order thickenings as in
Situation 91.9.1 / Definition 91.9.2 is a commutative square of ring sheaves with
epimorphic `kernelPullbackMap`. For an `O'`-module `F'` with `F = i^* F'` that is
flat over `O_{B'}`, finite presentation of `F'` as an `O'`-module is equivalent to
finite presentation of `F` as an `O`-module.
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
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {OB' OB O' O : Sheaf J CommRingCat.{max u v}}
variable {π : O' ⟶ O} {τ : OB' ⟶ OB}
variable [IsFirstOrderThickening π] [IsFirstOrderThickening τ]
variable [(restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable (f : OB ⟶ O) [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
variable (f' : OB' ⟶ O') (hcomm : f' ≫ π = τ ≫ f)
variable (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O')
variable [IsFlat OB' ((restrictionAlong f').obj F')]

/-- Lemma 91.11.3: Let `(f, f')` be a morphism of first-order thickenings of
ringed topoi as in Situation 91.9.1. Let `F'` be an `O'`-module and set
`F = i^* F'`. Assume that `F'` is flat over `O_{B'}` and that `(f, f')` is a
strict morphism of thickenings. Then `F'` is of finite presentation as an
`O'`-module if and only if `F` is of finite presentation as an `O`-module. -/
@[stacks 08VU]
theorem isFinitePresentation_iff (hstrict : IsStrict f f' hcomm) :
    F'.IsFinitePresentation ↔
      ((extendScalars (ringSheafMap π)).obj F').IsFinitePresentation := sorry

/-- Under a strict morphism of first-order thickenings, with `F'` flat over
`O_{B'}`, finite presentation of `i^* F'` implies finite presentation of `F'`. -/
theorem isFinitePresentation_of_extendScalars (hstrict : IsStrict f f' hcomm)
    [((extendScalars (ringSheafMap π)).obj F').IsFinitePresentation] :
    F'.IsFinitePresentation := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
