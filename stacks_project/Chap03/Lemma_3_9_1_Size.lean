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

open AlgebraicGeometry CategoryTheory
open scoped Cardinal AlgebraicGeometry

#check (AlgebraicGeometry.Scheme.size_eq :
  ∀ (X : Scheme.{u}),
    X.size = max (max ℵ₀ (#X.affineOpens)) (⨆ U : X.affineOpens, #(Γ(X, U))))

#check (AlgebraicGeometry.Scheme.cardinalMk_affineOpens_le_size :
  ∀ (X : Scheme.{u}), #X.affineOpens ≤ X.size)

#check (AlgebraicGeometry.Scheme.cardinalMk_sections_le_size :
  ∀ (X : Scheme.{u}) (U : X.affineOpens), #(Γ(X, U)) ≤ X.size)

#check (AlgebraicGeometry.Scheme.size_eq_of_iso :
  ∀ {X Y : Scheme.{u}} (e : X ≅ Y), X.size = Y.size)

#check (AlgebraicGeometry.Scheme.sizeLE :
  Cardinal.{u} → ObjectProperty Scheme.{u})

#check (AlgebraicGeometry.Scheme.sizeLE_iff :
  ∀ (κ : Cardinal.{u}) (X : Scheme.{u}), AlgebraicGeometry.Scheme.sizeLE κ X ↔ X.size ≤ κ)

#check (AlgebraicGeometry.Scheme.sizeLE.instIsClosedUnderIsomorphisms :
  ∀ (κ : Cardinal.{u}),
    ObjectProperty.IsClosedUnderIsomorphisms (AlgebraicGeometry.Scheme.sizeLE κ))

#check (AlgebraicGeometry.Scheme.sizeLE.essentiallySmall :
  ∀ (κ : Cardinal.{u}),
    ObjectProperty.EssentiallySmall.{u} (AlgebraicGeometry.Scheme.sizeLE κ))
