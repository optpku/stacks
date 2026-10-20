module

import ReasLib.AlgebraicGeometry.Scheme.Sites.ConstantGroup
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry CategoryTheory MonObj MonoidalCategory

universe u

/- Remark 59.23.2: the constant group sheaf is described by locally constant
sections, represented by the constant group scheme, and agrees with the selected
standard-topology sheafification on the big and small sites. -/
@[stacks 03P5] #check
  (AlgebraicGeometry.Scheme.constantGroupZariskiSections :
    ∀ (S : Scheme.{u}) (G : GrpCat.{u}) (U : Over S),
      [HasWeakSheafify (Scheme.zariskiTopology.over S) (Type (u + 1))] →
      ((CategoryTheory.constantSheaf (Scheme.zariskiTopology.over S) (Type (u + 1))).obj
          (ULift.{u + 1} (G : Type u))).obj.obj (op U) =
        ULift.{u + 1} (LocallyConstant U.left G))

#check (AlgebraicGeometry.Scheme.constantGroupZariskiRepresented :
  ∀ (S : Scheme.{u}) (G : GrpCat.{u}),
    [HasWeakSheafify (Scheme.zariskiTopology.over S) GrpCat.{u}] →
    CategoryTheory.IsIsomorphic
      ((CategoryTheory.constantSheaf (Scheme.zariskiTopology.over S) GrpCat.{u}).obj G).obj
      (CategoryTheory.yonedaGrp.obj (AlgebraicGeometry.ConstantGroup.baseChange S G)))

#check (AlgebraicGeometry.Scheme.constantGroupZariskiIsTauSheafification :
  ∀ (S : Scheme.{u}) (G : GrpCat.{u}) (τ : StandardTopology),
    [HasWeakSheafify (Scheme.zariskiTopology.over S) (Type (u + 1))] →
    [HasWeakSheafify (τ.overTopology S) (Type (u + 1))] →
    CategoryTheory.Presheaf.IsSheafification (τ.overTopology S)
      (CategoryTheory.toSheafify (Scheme.zariskiTopology.over S)
        ((Functor.const (Over S)ᵒᵖ).obj (ULift.{u + 1} (G : Type u)))))

#check (AlgebraicGeometry.Scheme.constantGroupSmallSections :
  ∀ (S : Scheme.{u}) (G : GrpCat.{u}) (U : S.smallZariskiSite),
    [HasWeakSheafify S.smallZariskiTopology (Type (u + 1))] →
    ((CategoryTheory.constantSheaf S.smallZariskiTopology (Type (u + 1))).obj
        (ULift.{u + 1} (G : Type u))).obj.obj (op U) =
      ULift.{u + 1} (LocallyConstant U.left G))

#check (AlgebraicGeometry.Scheme.constantGroupSmallRepresented :
  ∀ (S : Scheme.{u}) (G : GrpCat.{u}),
    [HasWeakSheafify S.smallZariskiTopology GrpCat.{u}] →
    CategoryTheory.IsIsomorphic
      ((CategoryTheory.constantSheaf S.smallZariskiTopology GrpCat.{u}).obj G).obj
      (S.smallZariskiForget.op ⋙
        CategoryTheory.yonedaGrp.obj (AlgebraicGeometry.ConstantGroup.baseChange S G)))

#check (AlgebraicGeometry.Scheme.constantGroupSmallEtaleSections :
  ∀ (S : Scheme.{u}) (G : GrpCat.{u}) (U : S.Etale),
    [HasWeakSheafify (Scheme.SiteRestriction.smallEtaleZariskiTopology S)
      (Type (u + 1))] →
    ((CategoryTheory.constantSheaf
        (Scheme.SiteRestriction.smallEtaleZariskiTopology S) (Type (u + 1))).obj
        (ULift.{u + 1} (G : Type u))).obj.obj (op U) =
      ULift.{u + 1} (LocallyConstant U.left G))

#check (AlgebraicGeometry.Scheme.constantGroupSmallEtaleRepresented :
  ∀ (S : Scheme.{u}) (G : GrpCat.{u}),
    [HasWeakSheafify (Scheme.SiteRestriction.smallEtaleZariskiTopology S) GrpCat.{u}] →
    CategoryTheory.IsIsomorphic
      ((CategoryTheory.constantSheaf
          (Scheme.SiteRestriction.smallEtaleZariskiTopology S) GrpCat.{u}).obj G).obj
      ((Scheme.Etale.forget S).op ⋙
        CategoryTheory.yonedaGrp.obj (AlgebraicGeometry.ConstantGroup.baseChange S G)))

#check (AlgebraicGeometry.Scheme.constantGroupSmallZariskiIsTauSheafification :
  ∀ (S : Scheme.{u}) (G : GrpCat.{u}),
    [HasWeakSheafify S.smallZariskiTopology (Type (u + 1))] →
    CategoryTheory.Presheaf.IsSheafification S.smallZariskiTopology
      (CategoryTheory.toSheafify S.smallZariskiTopology
        ((Functor.const S.smallZariskiSiteᵒᵖ).obj (ULift.{u + 1} (G : Type u)))))

#check (AlgebraicGeometry.Scheme.constantGroupSmallEtaleIsTauSheafification :
  ∀ (S : Scheme.{u}) (G : GrpCat.{u}),
    [HasWeakSheafify (Scheme.SiteRestriction.smallEtaleZariskiTopology S)
      (Type (u + 1))] →
    [HasWeakSheafify S.smallEtaleTopology (Type (u + 1))] →
    CategoryTheory.Presheaf.IsSheafification S.smallEtaleTopology
      (CategoryTheory.toSheafify
        (Scheme.SiteRestriction.smallEtaleZariskiTopology S)
        ((Functor.const S.Etaleᵒᵖ).obj (ULift.{u + 1} (G : Type u)))))
