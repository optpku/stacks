/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Size

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry
open scoped Cardinal AlgebraicGeometry

#check (AlgebraicGeometry.Scheme.size : Scheme.{u} → Cardinal.{u})

#check (AlgebraicGeometry.Scheme.aleph0_le_size :
  ∀ (X : Scheme.{u}), ℵ₀ ≤ X.size)

#check (AlgebraicGeometry.Scheme.cardinalMk_affineOpens_le_size :
  ∀ (X : Scheme.{u}), #X.affineOpens ≤ X.size)

#check (AlgebraicGeometry.Scheme.cardinalMk_sections_le_size :
  ∀ (X : Scheme.{u}) (U : X.affineOpens), #(Γ(X, U)) ≤ X.size)
