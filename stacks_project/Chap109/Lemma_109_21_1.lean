/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.SemistableGeneration
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.SchemeOverField
open SheafOfModules
open scoped AlgebraicGeometry

universe u

/- Lemma 109.21.1: the absence of a rational tail in the residue-field fibre
is equivalent to neighbourhood generation of the relative dualizing tensor power. -/
@[stacks 0E6Y] #check (AlgebraicGeometry.no_rational_tail_iff_dualizingTensorPower_counit_epi :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [AtWorstNodal f] [IsProper f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint]
    (h_unit : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom))
    (s : S)
    (hgenus : 1 ≤ cohomologyFinrank (f.fiberToSpecResidueField s)
        (unit (f.fiber s).ringCatSheaf : (f.fiber s).Modules) 1)
    {m : ℕ} (hm : 2 ≤ m),
    ¬ Nonempty (RationalTail (Over.mk (f.fiberToSpecResidueField s))) ↔
      ∃ U : S.Opens, s ∈ U ∧
        Epi ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).map
          (dualizingTensorPowerCounit f m)))
