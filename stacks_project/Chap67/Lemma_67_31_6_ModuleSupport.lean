/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support

/-!
# Support of abelian sheaves and module sheaves

The geometric stalk and support API is provided by the shared sheaf and module owners.
-/

open CategoryTheory AlgebraicGeometry AlgebraicSpace Opposite
open CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

#check (AlgebraicGeometry.AlgebraicSpace.abelianSectionsFunctor :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (p : FieldValuedPoint X),
      Sheaf (smallEtaleTopology (ofOver p.overObj)) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u})

#check (AlgebraicGeometry.AlgebraicSpace.abelianSectionsFunctor_obj :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (p : FieldValuedPoint X)
    (G : Sheaf (smallEtaleTopology (ofOver p.overObj)) AddCommGrpCat.{u}),
      (abelianSectionsFunctor p).obj G = G.obj.obj (op p.sourceObj))

#check (AlgebraicGeometry.AlgebraicSpace.abelianGeometricStalk :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})
    (xbar : GeometricPoint X),
      AddCommGrpCat.{u})

#check (AlgebraicGeometry.AlgebraicSpace.abelianGeometricStalk_eq :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})
    (xbar : GeometricPoint X),
      abelianGeometricStalk F xbar =
      (abelianSectionsFunctor xbar.toFieldValuedPoint).obj
        ((EtaleAdditive.inverseImage xbar.hom).obj F))

#check (AlgebraicGeometry.AlgebraicSpace.abelianGeometricStalk_isZero_iff_of_image_eq :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) (xbar tbar : GeometricPoint X)
    (himage : xbar.image = tbar.image),
      IsZero (abelianGeometricStalk F xbar) ↔ IsZero (abelianGeometricStalk F tbar))

#check (AlgebraicGeometry.AlgebraicSpace.abelianSheafSupport :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}),
      Set (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.mem_abelianSheafSupport_iff :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})
    (x : Points X),
      x ∈ abelianSheafSupport F ↔
      ∃ xbar : GeometricPoint X, xbar.image = x ∧ ¬ IsZero (abelianGeometricStalk F xbar))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.moduleSupport :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules),
      Set (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_moduleSupport_iff :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) (x : Points X),
      x ∈ moduleSupport F ↔
      ∃ xbar : GeometricPoint X, xbar.image = x ∧
        ¬ IsZero (abelianGeometricStalk
            ((SheafOfModules.toSheaf (structureSheaf X)).obj F) xbar))
