/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Frobenius
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Theorem 64.3.3 (The Baffling Theorem). -/
@[stacks 03SN] #check
  (AlgebraicGeometry.Scheme.absoluteFrobenius_etaleHq_constantZMod_eq_id :
    ∀ {p : ℕ} [Fact p.Prime] (X : Scheme.{u}) [IsCharP X p] (n j : ℕ),
      etaleHq_constant_pullback (absoluteFrobenius p X)
          (AddCommGrpCat.of (ULift.{u} (ZMod n))) j =
        𝟙 _)

#check
  (AlgebraicGeometry.Scheme.absoluteFrobenius_etaleHq_constantZMod_apply :
    ∀ {p : ℕ} [Fact p.Prime] (X : Scheme.{u}) [IsCharP X p] (n j : ℕ)
      (ξ : (Sheaf.functorH X.smallEtaleTopology j).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} (ZMod n))))),
      etaleHq_constant_pullback (absoluteFrobenius p X)
          (AddCommGrpCat.of (ULift.{u} (ZMod n))) j ξ =
        ξ)

end AlgebraicGeometry.Scheme
