/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.GroupScheme.Abelian
public import ReasLib.AlgebraicGeometry.Scheme.Regular

/-!
# Fppf cohomology of commutative group schemes

The additive sheaf of represented points gives the coefficients for fppf
cohomology and its restriction to the function field of an integral base.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry.GroupScheme

/-- The additive presheaf of scheme-valued points of a commutative group scheme,
with restriction given by precomposition. -/
def additiveFppfPresheaf {W : Scheme.{u}} (G : GroupScheme W) [IsCommMonObj G.X] :
    (Over W)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (Additive (U.unop ⟶ G.X))
  map f := AddCommGrpCat.ofHom (((yonedaGrp.obj G).map f).hom.toAdditive)
  map_id U := by
    apply AddCommGrpCat.ext
    intro s
    change Additive.ofMul (𝟙 U.unop ≫ s.toMul) = s
    rw [Category.id_comp]
    exact ofMul_toMul s
  map_comp f g := by
    apply AddCommGrpCat.ext
    intro s
    change Additive.ofMul ((g.unop ≫ f.unop) ≫ s.toMul) =
      Additive.ofMul (g.unop ≫ (f.unop ≫ s.toMul))
    exact congrArg Additive.ofMul (Category.assoc _ _ _)

/-- The additive presheaf represented by a commutative group scheme is an fppf sheaf. -/
theorem additiveFppfPresheaf_isSheaf {W : Scheme.{u}} (G : GroupScheme W)
    [IsCommMonObj G.X] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left)
      (additiveFppfPresheaf (W := W) G) :=
  sorry

/-- The additive fppf sheaf of scheme-valued points of a commutative group scheme. -/
def additiveFppfSheaf {W : Scheme.{u}} (G : GroupScheme W) [IsCommMonObj G.X] :
    Sheaf (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u} :=
  ⟨additiveFppfPresheaf (W := W) G, additiveFppfPresheaf_isSheaf (W := W) G⟩

/-- Evaluating the additive fppf sheaf gives the additive group of morphisms
to the group scheme. -/
theorem additiveFppfSheaf_obj {W : Scheme.{u}} (G : GroupScheme W)
    [IsCommMonObj G.X] (U : (Over W)ᵒᵖ) :
    (additiveFppfSheaf G).obj.obj U =
      AddCommGrpCat.of (Additive (U.unop ⟶ G.X)) :=
  rfl

/-- Restriction in the additive fppf sheaf is the additive form of Yoneda
precomposition. -/
theorem additiveFppfSheaf_map {W : Scheme.{u}} (G : GroupScheme W)
    [IsCommMonObj G.X] {U V : (Over W)ᵒᵖ} (f : U ⟶ V) :
    (additiveFppfSheaf G).obj.map f =
      AddCommGrpCat.ofHom (((yonedaGrp.obj G).map f).hom.toAdditive) :=
  rfl

/-- Restriction of first fppf cohomology of a commutative group scheme to the
function field is induced by the generic-point morphism. -/
def fppfH1RestrictFunctionField {W : Scheme.{u}} [IsIntegral W] (G : GroupScheme W)
    [IsCommMonObj G.X]
    [HasSheafify (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u})] :
    (additiveFppfSheaf G).H' 1 (Over.mk (𝟙 W)) ⟶
      (additiveFppfSheaf G).H' 1
        (Over.mk (W.fromSpecStalk (genericPoint W))) :=
  ((additiveFppfSheaf G).cohomologyPresheaf 1).map
    (Over.homMk (W.fromSpecStalk (genericPoint W))).op

/-- Function-field restriction is the cohomology-presheaf map along the
generic-point morphism. -/
theorem fppfH1RestrictFunctionField_def {W : Scheme.{u}} [IsIntegral W]
    (G : GroupScheme W) [IsCommMonObj G.X]
    [HasSheafify (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u})] :
    fppfH1RestrictFunctionField G =
      ((additiveFppfSheaf G).cohomologyPresheaf 1).map
        (Over.homMk (W.fromSpecStalk (genericPoint W))).op :=
  rfl

/-- For an abelian scheme over a two-dimensional regular integral Noetherian
scheme, restriction of first fppf cohomology to the function field is injective. -/
theorem fppfH1RestrictFunctionField_injective {W : Scheme.{u}}
    [IsIntegral W] [IsNoetherian W] [Scheme.Regular W]
    (hdim : topologicalKrullDim W = 2) (G : GroupScheme W) [AbelianScheme G]
    [HasSheafify (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u})] :
    Function.Injective (fppfH1RestrictFunctionField G).hom :=
  sorry

end AlgebraicGeometry.GroupScheme
