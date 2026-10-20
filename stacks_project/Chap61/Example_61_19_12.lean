module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.FunctionSheaf
import StacksCheckRecall

/-!
# Example 61.19.12

Point functions on the small pro-étale site, their quotient by the constant
sheaf, and the affine section formula over schemes with closed separably
closed points.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProEt

noncomputable section

universe u

/- Example 61.19.12: the sheaf of all point-set maps on the small pro-étale site. -/
@[stacks 0F6D]
#check (AlgebraicGeometry.Scheme.ProEt.functionSheaf :
  ∀ (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A],
    Sheaf (topology X) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.Scheme.ProEt.functionSheaf_obj :
  ∀ (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A] (U : X.ProEt),
    (functionSheaf X A).obj.obj (op U) = AddCommGrpCat.of (U.left → A))

#check (AlgebraicGeometry.Scheme.ProEt.constantToFunction_app_eq :
  ∀ (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}] (U : X.ProEt),
    (toSheafify (topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app (op U) ≫
        (constantToFunction X A).hom.app (op U) =
      AddCommGrpCat.ofHom (Pi.constAddMonoidHom U.left A))

#check (AlgebraicGeometry.Scheme.ProEt.functionsModLocallyConstantSequence_shortExact :
  ∀ (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}],
    (functionsModLocallyConstantSequence X A).ShortExact)

#check (AlgebraicGeometry.Scheme.ProEt.constantSheaf_etaleToProEtPullback_isIsomorphic :
  ∀ (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleToProEt X).op.HasLeftKanExtension F]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}],
    IsIsomorphic
      ((etaleToProEtPullback X AddCommGrpCat.{u + 1}).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of A)))
      ((constantSheaf (topology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of A)))

#check (AlgebraicGeometry.Scheme.ProEt.functionSheaf_not_mem_essImage :
  ∀ (X : Scheme.{u}), Nonempty X → ∀ (A : Type (u + 1)) [AddCommGroup A] [Nontrivial A]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleToProEt X).op.HasLeftKanExtension F]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}],
    ¬ (etaleToProEtPullback X AddCommGrpCat.{u + 1}).essImage (functionSheaf X A))

#check (AlgebraicGeometry.Scheme.ProEt.functionsModLocallyConstant_not_mem_essImage :
  ∀ (X : Scheme.{u}), Nonempty X → ∀ (A : Type (u + 1)) [AddCommGroup A] [Nontrivial A]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleToProEt X).op.HasLeftKanExtension F]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}],
    ¬ (etaleToProEtPullback X AddCommGrpCat.{u + 1}).essImage
        (functionsModLocallyConstant X A))

#check (AlgebraicGeometry.Scheme.isClosed_singleton_of_weaklyEtale :
  ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f],
    (∀ x : X, IsClosed ({x} : Set X)) → ∀ y : Y, IsClosed ({y} : Set Y))

#check (AlgebraicGeometry.Scheme.isSepClosed_residueField_of_weaklyEtale :
  ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f],
    (∀ x : X, IsSepClosed (X.residueField x)) →
      ∀ y : Y, IsSepClosed (Y.residueField y))

section EtaleVanishing

variable (Y : Scheme.{u}) [IsAffine Y]
    (h_closed : ∀ y : Y, IsClosed ({y} : Set Y))
    (h_res : ∀ y : Y, IsSepClosed (Y.residueField y))
    (A : Type (u + 1)) [AddCommGroup A]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

#check (AlgebraicGeometry.Scheme.etaleCohomology_isZero_of_affine_closedPoints_sepClosedResidue
    Y h_closed h_res
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of A)) 1 (by decide) :
  IsZero ((Sheaf.functorH Y.smallEtaleTopology 1).obj
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of A))))

end EtaleVanishing

#check (AlgebraicGeometry.Scheme.ProEt.proEtH1_constant_isZero :
  ∀ (Y : Scheme.{u}) [IsAffine Y],
    (∀ y : Y, IsClosed ({y} : Set Y)) →
    (∀ y : Y, IsSepClosed (Y.residueField y)) →
    ∀ (A : Type (u + 1)) [AddCommGroup A]
    [HasSheafify (topology Y) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (topology Y) AddCommGrpCat.{u + 1})],
    IsZero ((Sheaf.functorH (topology Y) 1).obj
      ((constantSheaf (topology Y) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of A))))

#check (AlgebraicGeometry.Scheme.ProEt.functionsModLocallyConstant_sections :
  ∀ (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A],
    (∀ x : X, IsClosed ({x} : Set X)) →
    (∀ x : X, IsSepClosed (X.residueField x)) →
    ∀ (U : X.ProEt) [IsAffine U.left]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}],
    IsIsomorphic ((functionsModLocallyConstant X A).obj.obj (op U))
      (cokernel ((constantToFunction X A).hom.app (op U))))
