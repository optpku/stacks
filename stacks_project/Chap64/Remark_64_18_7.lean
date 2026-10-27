/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Torsion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace ZEllSheaf

/- Remark 64.18.7: on a Noetherian scheme, a `ℤ_[ℓ]`-sheaf is torsion if and only if
every geometric stalk is a torsion `ℤ_[ℓ]`-module. -/
@[stacks 03US]
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.isTorsion_iff_forall_stalk_isTorsion :
  ∀ {X : Scheme.{u}} [IsNoetherian X] {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
    (F : ZEllSheaf X ℓ),
    F.IsTorsion ↔ ∀ x : GeometricPoint X, Module.IsTorsion ℤ_[ℓ] (F.stalk x))

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
