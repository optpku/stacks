/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Jacobson.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Reduced.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Regular.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Smooth
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- The fpqc, fppf, and syntomic topologies are stronger than the smooth
topology, so locality for those precoverages implies smooth locality. -/

/- Remark 100.7.3 (1): local Noetherianity of schemes is local for the smooth
precoverage. -/
@[stacks 04YH] #check
  (AlgebraicGeometry.IsLocallyNoetherian.smoothLocal :
    ObjectProperty.IsLocal
      (IsLocallyNoetherian : ObjectProperty Scheme.{u}) Scheme.bigSmoothPrecoverage)

/- Remark 100.7.3 (2): the Jacobson property of schemes is local for the smooth
precoverage. -/
@[stacks 04YH] #check
  (AlgebraicGeometry.Scheme.JacobsonSpace.smoothLocal :
    ObjectProperty.IsLocal
      (fun X : Scheme.{u} ↦ JacobsonSpace X) Scheme.bigSmoothPrecoverage)

/- Remark 100.7.3 (3): being locally Noetherian and satisfying `(S_k)` is local
for the smooth precoverage. -/
@[stacks 04YH] #check
  (AlgebraicGeometry.Scheme.satisfiesSerreConditionS.smoothLocal :
    ∀ k : ℕ,
      ObjectProperty.IsLocal
        (fun X : Scheme.{u} ↦
          IsLocallyNoetherian X ∧ Scheme.satisfiesSerreConditionS X k)
        Scheme.bigSmoothPrecoverage)

/- Remark 100.7.3 (4): Cohen–Macaulayness of schemes is local for the smooth
precoverage. -/
@[stacks 04YH] #check
  (AlgebraicGeometry.Scheme.CohenMacaulay.smoothLocal :
    ObjectProperty.IsLocal
      (Scheme.CohenMacaulay : ObjectProperty Scheme.{u}) Scheme.bigSmoothPrecoverage)

/- Remark 100.7.3 (5): reducedness of schemes is local for the smooth
precoverage. -/
@[stacks 04YH] #check
  (AlgebraicGeometry.IsReduced.smoothLocal :
    ObjectProperty.IsLocal
      (IsReduced : ObjectProperty Scheme.{u}) Scheme.bigSmoothPrecoverage)

/- Remark 100.7.3 (6): normality of schemes is local for the smooth precoverage. -/
@[stacks 04YH] #check
  (AlgebraicGeometry.Scheme.isNormal.smoothLocal :
    ObjectProperty.IsLocal
      (Scheme.isNormal : ObjectProperty Scheme.{u}) Scheme.bigSmoothPrecoverage)

/- Remark 100.7.3 (7): being locally Noetherian and satisfying `(R_k)` is local
for the smooth precoverage. -/
@[stacks 04YH] #check
  (AlgebraicGeometry.Scheme.satisfiesSerreConditionR.smoothLocal :
    ∀ k : ℕ,
      ObjectProperty.IsLocal
        (fun X : Scheme.{u} ↦
          IsLocallyNoetherian X ∧ Scheme.satisfiesSerreConditionR X k)
        Scheme.bigSmoothPrecoverage)

/- Remark 100.7.3 (8): regularity of schemes is local for the smooth precoverage. -/
@[stacks 04YH] #check
  (AlgebraicGeometry.Scheme.Regular.smoothLocal :
    ObjectProperty.IsLocal
      (Scheme.Regular : ObjectProperty Scheme.{u}) Scheme.bigSmoothPrecoverage)

/- Remark 100.7.3 (9): the Nagata property of schemes is local for the smooth
precoverage. -/
@[stacks 04YH] #check
  (AlgebraicGeometry.Scheme.Nagata.smoothLocal :
    ObjectProperty.IsLocal
      (Scheme.Nagata : ObjectProperty Scheme.{u}) Scheme.bigSmoothPrecoverage)
