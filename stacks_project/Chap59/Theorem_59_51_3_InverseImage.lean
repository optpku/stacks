/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseSystem

/-! This source-facing module re-exports the reusable inverse-system API,
with original transitions indexed by the preorder category with adjoined identities. -/

#check AlgebraicGeometry.Scheme.Etale.transitionPullback
#check AlgebraicGeometry.Scheme.Etale.transitionPullbackCompIso
#check AlgebraicGeometry.Scheme.Etale.AbelianSheafSystem
#check AlgebraicGeometry.Scheme.Etale.AbelianSheafSystem.of
#check AlgebraicGeometry.Scheme.Etale.AbelianSheafSystem.of_obj
#check AlgebraicGeometry.Scheme.Etale.AbelianSheafSystem.of_transition
#check AlgebraicGeometry.Scheme.Etale.conePullback
#check AlgebraicGeometry.Scheme.Etale.coneLeg_isContinuous
#check AlgebraicGeometry.Scheme.Etale.coneLeg_sheafPushforward_isRightAdjoint
#check AlgebraicGeometry.Scheme.Etale.coneLegSheafAdjunction
#check AlgebraicGeometry.Scheme.Etale.conePullbackCompIso
#check AlgebraicGeometry.Scheme.Etale.inverseImageDiagram
#check AlgebraicGeometry.Scheme.Etale.colimitInverseImage
#check AlgebraicGeometry.Scheme.Etale.colimitInverseImage_ι
#check AlgebraicGeometry.Scheme.Etale.colimitInverseImage_ι_eq
