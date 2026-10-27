/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

variable {X : Scheme.{u}} [IsNoetherian X] {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/-- An integral ℓ-adic sheaf is constructible when every stage is constructible
on the small étale site. -/
def IsConstructible (F : ZEllSheaf X ℓ) : Prop :=
  ∀ n, IsConstructibleEtale
    (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦
      ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
        X.smallEtaleTopology Y.smallEtaleTopology).obj)
    (fun {Y : Scheme.{u}} (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
      IsFiniteLocallyConstantAddCommGrp G) (F.stage n)

/-- Every integral ℓ-adic sheaf has constructible stages. -/
theorem constructible (F : ZEllSheaf X ℓ) : F.IsConstructible := F.isConstructible

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
