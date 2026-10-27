/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.VectorBundle.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition

/-! # Geometric properties of associated line bundles on algebraic spaces -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The structure morphism of the associated line bundle is flat. -/
instance instFlat_associatedVectorBundleπ (L : X.Modules)
    [isInvertibleObject L] : Flat (associatedVectorBundleπ L) :=
  sorry

/-- The structure morphism of the associated line bundle has relative dimension `1`. -/
instance instRelativeDimension_associatedVectorBundleπ (L : X.Modules)
    [isInvertibleObject L] : RelativeDimension (associatedVectorBundleπ L) 1 :=
  sorry

/-- The structure morphism of the associated line bundle is quasi-separated. -/
instance instQuasiSeparated_associatedVectorBundleπ (L : X.Modules)
    [isInvertibleObject L] : QuasiSeparated (associatedVectorBundleπ L) :=
  sorry

/-- The structure morphism of the associated line bundle is locally of finite type. -/
instance instLocallyOfFiniteType_associatedVectorBundleπ (L : X.Modules)
    [isInvertibleObject L] : LocallyOfFiniteType (associatedVectorBundleπ L) :=
  sorry

/-- Composition of the associated-vector-bundle projection with a quasi-separated
morphism remains quasi-separated. -/
instance instQuasiSeparated_associatedVectorBundleπ_comp {B : AlgebraicSpace S}
    (pX : X ⟶ B) (L : X.Modules) [isInvertibleObject L] [QuasiSeparated pX] :
    QuasiSeparated (associatedVectorBundleπ L ≫ pX) :=
  quasiSeparated_comp (associatedVectorBundleπ L) pX

/-- Composition of the associated-vector-bundle projection with a locally finite
type morphism remains locally of finite type. -/
instance instLocallyOfFiniteType_associatedVectorBundleπ_comp
    {B : AlgebraicSpace S} (pX : X ⟶ B) (L : X.Modules) [isInvertibleObject L]
    [LocallyOfFiniteType pX] :
    LocallyOfFiniteType (associatedVectorBundleπ L ≫ pX) :=
  locallyOfFiniteType_comp (associatedVectorBundleπ L) pX

end AlgebraicGeometry.AlgebraicSpace
