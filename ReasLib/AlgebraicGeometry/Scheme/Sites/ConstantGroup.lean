/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ConstantGroup
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Small
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.PullbackSections
public import ReasLib.CategoryTheory.Sites.Sheafification.Map
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry CategoryTheory MonObj MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme

/-- The sections of the constant sheaf on the big Zariski site are locally constant maps. -/
theorem constantGroupZariskiSections
    (S : Scheme.{u}) (G : GrpCat.{u}) (U : Over S)
    [HasWeakSheafify (Scheme.zariskiTopology.over S) (Type (u + 1))] :
    ((CategoryTheory.constantSheaf (Scheme.zariskiTopology.over S) (Type (u + 1))).obj
        (ULift.{u + 1} (G : Type u))).obj.obj (op U) =
      ULift.{u + 1} (LocallyConstant U.left G) := sorry

/-- The constant sheaf on the big Zariski site is represented by the constant group scheme. -/
theorem constantGroupZariskiRepresented
    (S : Scheme.{u}) (G : GrpCat.{u})
    [HasWeakSheafify (Scheme.zariskiTopology.over S) GrpCat.{u}] :
    CategoryTheory.IsIsomorphic
      ((CategoryTheory.constantSheaf (Scheme.zariskiTopology.over S) GrpCat.{u}).obj G).obj
      (CategoryTheory.yonedaGrp.obj (AlgebraicGeometry.ConstantGroup.baseChange S G)) := sorry

/-- The big Zariski sheafification presents the constant sheaf for every standard topology. -/
theorem constantGroupZariskiIsTauSheafification
    (S : Scheme.{u}) (G : GrpCat.{u}) (τ : StandardTopology)
    [HasWeakSheafify (Scheme.zariskiTopology.over S) (Type (u + 1))]
    [HasWeakSheafify (τ.overTopology S) (Type (u + 1))] :
    CategoryTheory.Presheaf.IsSheafification (τ.overTopology S)
      (CategoryTheory.toSheafify (Scheme.zariskiTopology.over S)
        ((Functor.const (Over S)ᵒᵖ).obj (ULift.{u + 1} (G : Type u)))) := sorry

/-- The sections of the constant sheaf on the small Zariski site are locally constant maps. -/
theorem constantGroupSmallSections
    (S : Scheme.{u}) (G : GrpCat.{u}) (U : S.smallZariskiSite)
    [HasWeakSheafify S.smallZariskiTopology (Type (u + 1))] :
    ((CategoryTheory.constantSheaf S.smallZariskiTopology (Type (u + 1))).obj
        (ULift.{u + 1} (G : Type u))).obj.obj (op U) =
      ULift.{u + 1} (LocallyConstant U.left G) := sorry

/-- The constant sheaf on the small Zariski site is represented by the restricted constant group scheme. -/
theorem constantGroupSmallRepresented
    (S : Scheme.{u}) (G : GrpCat.{u})
    [HasWeakSheafify S.smallZariskiTopology GrpCat.{u}] :
    CategoryTheory.IsIsomorphic
      ((CategoryTheory.constantSheaf S.smallZariskiTopology GrpCat.{u}).obj G).obj
      (S.smallZariskiForget.op ⋙
        CategoryTheory.yonedaGrp.obj (AlgebraicGeometry.ConstantGroup.baseChange S G)) := sorry

/-- The sections of the constant sheaf for the induced Zariski topology on the small étale site are locally constant maps. -/
theorem constantGroupSmallEtaleSections
    (S : Scheme.{u}) (G : GrpCat.{u}) (U : S.Etale)
    [HasWeakSheafify (Scheme.SiteRestriction.smallEtaleZariskiTopology S)
      (Type (u + 1))] :
    ((CategoryTheory.constantSheaf
        (Scheme.SiteRestriction.smallEtaleZariskiTopology S) (Type (u + 1))).obj
        (ULift.{u + 1} (G : Type u))).obj.obj (op U) =
      ULift.{u + 1} (LocallyConstant U.left G) := sorry

/-- The constant sheaf for the induced Zariski topology on the small étale site is represented by the restricted constant group scheme. -/
theorem constantGroupSmallEtaleRepresented
    (S : Scheme.{u}) (G : GrpCat.{u})
    [HasWeakSheafify (Scheme.SiteRestriction.smallEtaleZariskiTopology S) GrpCat.{u}] :
    CategoryTheory.IsIsomorphic
      ((CategoryTheory.constantSheaf
          (Scheme.SiteRestriction.smallEtaleZariskiTopology S) GrpCat.{u}).obj G).obj
      ((Scheme.Etale.forget S).op ⋙
        CategoryTheory.yonedaGrp.obj (AlgebraicGeometry.ConstantGroup.baseChange S G)) := sorry

/-- The small Zariski sheafification presents the constant sheaf for the small Zariski topology. -/
theorem constantGroupSmallZariskiIsTauSheafification
    (S : Scheme.{u}) (G : GrpCat.{u})
    [HasWeakSheafify S.smallZariskiTopology (Type (u + 1))] :
    CategoryTheory.Presheaf.IsSheafification S.smallZariskiTopology
      (CategoryTheory.toSheafify S.smallZariskiTopology
        ((Functor.const S.smallZariskiSiteᵒᵖ).obj (ULift.{u + 1} (G : Type u)))) := sorry

/-- The induced Zariski sheafification on the small étale site presents the constant sheaf for the étale topology. -/
theorem constantGroupSmallEtaleIsTauSheafification
    (S : Scheme.{u}) (G : GrpCat.{u})
    [HasWeakSheafify (Scheme.SiteRestriction.smallEtaleZariskiTopology S)
      (Type (u + 1))]
    [HasWeakSheafify S.smallEtaleTopology (Type (u + 1))] :
    CategoryTheory.Presheaf.IsSheafification S.smallEtaleTopology
      (CategoryTheory.toSheafify
        (Scheme.SiteRestriction.smallEtaleZariskiTopology S)
        ((Functor.const S.Etaleᵒᵖ).obj (ULift.{u + 1} (G : Type u)))) := sorry

end AlgebraicGeometry.Scheme
