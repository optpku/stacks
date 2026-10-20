/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Adic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.CompactSupport

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace ZEllSheaf

section Global

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]

/- Definition 64.18.8: the global ℓ-adic cohomology API is provided by the
reusable inverse-limit owner. -/
#check (ZEllSheaf.cohomology : ZEllSheaf X ℓ → ℕ → AddCommGrpCat.{u})

end Global

section CompactSupport

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable {X : SchemeOverField k} [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [IsNoetherian X.left]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [Etale (Compactification.Of.ι P)]
variable [∀ G : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u})]

/- Definition 64.18.8: the compact-support ℓ-adic cohomology API is parameterized
by an explicit compactification. -/
#check (ZEllSheaf.cohomologyCompactSupport P :
  ZEllSheaf X.left ℓ → ℕ → AddCommGrpCat.{u})

/- Definition 64.18.8: the `ℚ_[ℓ]` compact-support API is scalar extension of
the integral module-valued API. -/
#check (ZEllSheaf.cohomologyCompactSupportQEll P :
  ZEllSheaf X.left ℓ → ℕ → ModuleCat.{u} ℚ_[ℓ])

end CompactSupport

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
