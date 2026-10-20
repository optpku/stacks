/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IndQuasiAffine.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IndQuasiAffine.Basic

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

#check (AlgebraicGeometry.Scheme.IsIndQuasiAffine :
  AlgebraicGeometry.Scheme.{u} → Prop)

#check (@AlgebraicGeometry.Scheme.IsQuasiAffine.isIndQuasiAffine :
  ∀ (X : AlgebraicGeometry.Scheme.{u}),
    AlgebraicGeometry.Scheme.IsQuasiAffine X →
      AlgebraicGeometry.Scheme.IsIndQuasiAffine X)

#check (AlgebraicGeometry.Scheme.isIndQuasiAffine_iff :
  ∀ (X : AlgebraicGeometry.Scheme.{u}),
    X.IsIndQuasiAffine ↔
      ∀ (U : X.Opens), IsCompact (U : Set X) → U.toScheme.IsQuasiAffine)

#check (AlgebraicGeometry.Scheme.Hom.IsQuasiAffineOnCompactOpens :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.Scheme.Hom.isQuasiAffineOnCompactOpens_iff :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y),
    g.IsQuasiAffineOnCompactOpens ↔
      ∀ (U : X.Opens), IsCompact (U : Set X) →
        AlgebraicGeometry.QuasiAffineHom (U.ι ≫ g))

#check (@AlgebraicGeometry.IndQuasiAffineHom :
  CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})

#check (AlgebraicGeometry.indQuasiAffineHom_iff_affineOpens :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
    AlgebraicGeometry.IndQuasiAffineHom f ↔
      ∀ V : Y.affineOpens,
        (f ⁻¹ᵁ (V : Y.Opens)).toScheme.IsIndQuasiAffine)
