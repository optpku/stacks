/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Jacobson.Etale
public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition.Etale
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Reduced.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Regular.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Etale
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- The fpqc, fppf, syntomic, and smooth topologies are stronger than the étale
topology, so locality for those precoverages implies étale locality. -/

/- Remark 66.7.3 (1): local Noetherianity of schemes is local for the étale
precoverage. -/
@[stacks 03E7] #check
  (AlgebraicGeometry.IsLocallyNoetherian.isLocalEtale :
    ObjectProperty.IsLocal
      (IsLocallyNoetherian : ObjectProperty Scheme.{u}) Scheme.etalePrecoverage)

/- Remark 66.7.3 (2): the Jacobson property of schemes is local for the étale
precoverage. -/
@[stacks 03E7] #check
  (AlgebraicGeometry.Scheme.JacobsonSpace.isLocalEtale :
    ObjectProperty.IsLocal
      (fun X : Scheme.{u} ↦ JacobsonSpace X) Scheme.etalePrecoverage)

/- Remark 66.7.3 (3): being locally Noetherian and satisfying `(S_k)` is local
for the étale precoverage. -/
@[stacks 03E7] #check
  (AlgebraicGeometry.Scheme.satisfiesSerreConditionS.isLocalEtale :
    ∀ k : ℕ,
      ObjectProperty.IsLocal
        (fun X : Scheme.{u} ↦
          IsLocallyNoetherian X ∧ Scheme.satisfiesSerreConditionS X k)
        Scheme.etalePrecoverage)

/- Remark 66.7.3 (4): Cohen–Macaulayness of schemes is local for the étale
precoverage. -/
@[stacks 03E7] #check
  (AlgebraicGeometry.Scheme.CohenMacaulay.isLocalEtale :
    ObjectProperty.IsLocal
      (Scheme.CohenMacaulay : ObjectProperty Scheme.{u}) Scheme.etalePrecoverage)

/- Remark 66.7.3 (5): Gorensteinness of schemes is local for the étale
precoverage. -/
@[stacks 03E7] #check
  (AlgebraicGeometry.Scheme.Gorenstein.isLocalEtale :
    ObjectProperty.IsLocal
      (Scheme.Gorenstein : ObjectProperty Scheme.{u}) Scheme.etalePrecoverage)

/- Remark 66.7.3 (6): reducedness of schemes is local for the étale
precoverage. -/
@[stacks 03E7] #check
  (AlgebraicGeometry.IsReduced.isLocalEtale :
    ObjectProperty.IsLocal
      (IsReduced : ObjectProperty Scheme.{u}) Scheme.etalePrecoverage)

/- Remark 66.7.3 (7): normality of schemes is local for the étale precoverage. -/
@[stacks 03E7] #check
  (AlgebraicGeometry.Scheme.isNormal.isLocalEtale :
    ObjectProperty.IsLocal
      (Scheme.isNormal : ObjectProperty Scheme.{u}) Scheme.etalePrecoverage)

/- Remark 66.7.3 (8): being locally Noetherian and satisfying `(R_k)` is local
for the étale precoverage. -/
@[stacks 03E7] #check
  (AlgebraicGeometry.Scheme.satisfiesSerreConditionR.isLocalEtale :
    ∀ k : ℕ,
      ObjectProperty.IsLocal
        (fun X : Scheme.{u} ↦
          IsLocallyNoetherian X ∧ Scheme.satisfiesSerreConditionR X k)
        Scheme.etalePrecoverage)

/- Remark 66.7.3 (9): regularity of schemes is local for the étale precoverage. -/
@[stacks 03E7] #check
  (AlgebraicGeometry.Scheme.Regular.isLocalEtale :
    ObjectProperty.IsLocal
      (Scheme.Regular : ObjectProperty Scheme.{u}) Scheme.etalePrecoverage)

/- Remark 66.7.3 (10): the Nagata property of schemes is local for the étale
precoverage. -/
@[stacks 03E7] #check
  (AlgebraicGeometry.Scheme.Nagata.isLocalEtale :
    ObjectProperty.IsLocal
      (Scheme.Nagata : ObjectProperty Scheme.{u}) Scheme.etalePrecoverage)
