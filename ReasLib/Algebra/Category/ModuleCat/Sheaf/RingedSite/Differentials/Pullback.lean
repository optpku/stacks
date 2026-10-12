/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pulling back morphisms induced by relative derivations

This file isolates the generic universal-property step behind pullback maps on relative
differentials.  A relative derivation with values in a pushforward module first descends from
the relative-differentials sheaf and is then transposed across the pullback-pushforward
adjunction.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RelativeDerivation

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {F : C ⥤ D} [F.IsContinuous J K]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}
variable {R : Sheaf K RingCat.{max u v}}
variable {alpha : ringSheaf J O₂ ⟶
  (F.sheafPushforwardContinuous RingCat.{max u v} J K).obj R}
variable [(SheafOfModules.pushforward alpha).IsRightAdjoint]
variable {M : SheafOfModules R} {phi : O₁ ⟶ O₂}

/-- A morphism out of the pullback of `relativeDifferentials phi` is induced by a relative
derivation with values in the corresponding pushforward module. -/
@[stacks 04BR "universal pullback descent"]
noncomputable def pullbackDesc
    (derivation : SheafOfModules.RelativeDerivation phi
      ((SheafOfModules.pushforward alpha).obj M)) :
    (SheafOfModules.pullback alpha).obj (relativeDifferentials phi) ⟶ M :=
  ((SheafOfModules.pullbackPushforwardAdjunction alpha).homEquiv _ _).symm
    (relativeDifferentialDesc phi derivation)

/-- The universal-property predicate characterizing `pullbackDesc derivation`. -/
def IsPullbackDesc
    (derivation : SheafOfModules.RelativeDerivation phi
      ((SheafOfModules.pushforward alpha).obj M))
    (tau : (SheafOfModules.pullback alpha).obj (relativeDifferentials phi) ⟶ M) : Prop :=
  (relativeDifferential phi).postcomp
      (((SheafOfModules.pullbackPushforwardAdjunction alpha).homEquiv _ _) tau).val =
    derivation

/-- Transposing `pullbackDesc derivation` recovers the morphism descended from the relative
derivation. -/
theorem pullbackDesc_homEquiv
    (derivation : SheafOfModules.RelativeDerivation phi
      ((SheafOfModules.pushforward alpha).obj M)) :
    ((SheafOfModules.pullbackPushforwardAdjunction alpha).homEquiv _ _)
        (pullbackDesc derivation) =
      relativeDifferentialDesc phi derivation := sorry

/-- The morphism `pullbackDesc derivation` induces the original relative derivation. -/
theorem pullbackDesc_isPullbackDesc
    (derivation : SheafOfModules.RelativeDerivation phi
      ((SheafOfModules.pushforward alpha).obj M)) :
    IsPullbackDesc derivation (pullbackDesc derivation) := sorry

/-- A morphism satisfying the pullback descent property is the canonical descended morphism. -/
theorem eq_pullbackDesc
    (derivation : SheafOfModules.RelativeDerivation phi
      ((SheafOfModules.pushforward alpha).obj M))
    {tau : (SheafOfModules.pullback alpha).obj (relativeDifferentials phi) ⟶ M}
    (h_tau : IsPullbackDesc derivation tau) :
    tau = pullbackDesc derivation := sorry

/-- The pullback descent property determines a unique morphism. -/
theorem existsUnique_isPullbackDesc
    (derivation : SheafOfModules.RelativeDerivation phi
      ((SheafOfModules.pushforward alpha).obj M)) :
    ∃! tau : (SheafOfModules.pullback alpha).obj (relativeDifferentials phi) ⟶ M,
      IsPullbackDesc derivation tau := sorry

end SheafOfModules.RelativeDerivation
