/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.LFunction
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

variable {k : Type u} [Field k] [Fintype k]
variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom] [IsNoetherian X.left]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/- Definition 64.19.3: if F is a ℚ_[ℓ]-sheaf on a finite-type scheme X over a
finite field k, viewed as a ℤ_[ℓ]-sheaf with geometric stalks F.qellStalk, the
L-function is the Euler product
L(X, F) := ∏_{x ∈ closedPoints X} det(1 - π_x^* T^{deg x} | F_x̄)⁻¹
in PowerSeries ℚ_[ℓ], where deg x = X.hom.residueDegree x, π_x^* is
ZEllSheaf.geometricFrobeniusStalk, and F_x̄ is F.qellStalk at
geometricPointOverClosedPoint. The product converges because there are only
finitely many closed points of each residue degree. -/
@[stacks 03UX] #check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.lFunction :
  ∀ (F : ZEllSheaf X.left ℓ), F.IsConstructible → PowerSeries ℚ_[ℓ])
