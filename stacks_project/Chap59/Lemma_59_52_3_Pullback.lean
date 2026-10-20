/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Hypercohomology.BaseChange

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {S T U : Scheme.{u}} (f : U ⟶ T) (g : T ⟶ S)
variable [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ {S T : Scheme.{u}} (g : T ⟶ S),
  ((smallEtalePullback g).sheafPushforwardContinuous AddCommGrpCat.{u}
    S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
variable (K : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) ℤ)

/- The canonical compatibility isomorphism for successive inverse images. -/
#check
  (AlgebraicGeometry.Scheme.Etale.inverseImageComplexCompIso f g K :
    inverseImageComplex f (inverseImageComplex g K) ≅
      inverseImageComplex (f ≫ g) K)

end AlgebraicGeometry.Scheme.Etale

end
