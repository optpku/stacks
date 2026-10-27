/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition

/-! # Geometric properties of algebraic-space pullbacks -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structure morphism of a pullback followed by a good morphism is
quasi-separated. -/
instance quasiSeparated_pullbackFst_comp_structure
    {S : Scheme.{u}} {B X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (pZ : Z ⟶ B)
    {Y' : AlgebraicSpace S} (i : Y' ⟶ Y)
    [QuasiSeparated (i ≫ g ≫ pZ)]
    [QuasiSeparated ((f ≫ g) ≫ pZ)] :
    QuasiSeparated (pullback.fst f i ≫ (f ≫ g) ≫ pZ) := sorry

/-- The structure morphism of a pullback followed by a good morphism is
locally of finite type. -/
instance locallyOfFiniteType_pullbackFst_comp_structure
    {S : Scheme.{u}} {B X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (pZ : Z ⟶ B)
    {Y' : AlgebraicSpace S} (i : Y' ⟶ Y)
    [LocallyOfFiniteType (i ≫ g ≫ pZ)]
    [LocallyOfFiniteType ((f ≫ g) ≫ pZ)] :
    LocallyOfFiniteType (pullback.fst f i ≫ (f ≫ g) ≫ pZ) := sorry

end AlgebraicGeometry.AlgebraicSpace
