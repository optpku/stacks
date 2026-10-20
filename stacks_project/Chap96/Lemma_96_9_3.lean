module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.ComparisonProperties
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.InverseImage

/-!
# Lemma 96.9.3

Functoriality, étaleness, and inverse-image compatibility of the small-étale
comparison morphism `c_φ`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite
open AlgebraicGeometry.GroupoidsOver FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Scheme
open scoped Bicategory

noncomputable section

universe u

variable {S : Scheme.{u}} {X : GroupoidsOver S}

section ComparisonComp

variable {x y z : X.total} (φ : x ⟶ y) (ψ : y ⟶ z)
variable (F : Sheaf X.etaleTopology (Type (u + 1)))
variable [HasWeakSheafify (X.p.obj x).left.smallEtaleTopology (Type (u + 1))]
variable [HasWeakSheafify (X.p.obj y).left.smallEtaleTopology (Type (u + 1))]
variable [∀ P : (X.p.obj y).left.Etaleᵒᵖ ⥤ Type (u + 1),
    (smallEtalePullback (X.p.map φ).left).op.HasLeftKanExtension P]
variable [∀ P : (X.p.obj z).left.Etaleᵒᵖ ⥤ Type (u + 1),
    (smallEtalePullback (X.p.map ψ).left).op.HasLeftKanExtension P]
variable [∀ P : (X.p.obj z).left.Etaleᵒᵖ ⥤ Type (u + 1),
    (smallEtalePullback (X.p.map (φ ≫ ψ)).left).op.HasLeftKanExtension P]
variable [∀ P : (X.p.obj z).left.Etaleᵒᵖ ⥤ Type (u + 1),
    (smallEtalePullback ((X.p.map φ).left ≫ (X.p.map ψ).left)).op.HasLeftKanExtension P]

/- Lemma 96.9.3 (1): If φ : x ⟶ y and ψ : y ⟶ z are morphisms of X lying over
a : U ⟶ V and b : V ⟶ W, then the composition a_small⁻¹(c_ψ) then c_φ equals
c_{ψ ∘ φ} via the identification (b ∘ a)_small⁻¹ = a_small⁻¹ ∘ b_small⁻¹. -/
@[stacks 075D]
#check (AlgebraicGeometry.GroupoidsOver.comparison_comp φ ψ F :
    comparison (φ ≫ ψ) F =
      (eqToHom (congrArg
        (fun a : (X.p.obj x).left ⟶ (X.p.obj z).left ↦
          (EtaleSheaf.pullback a).obj (restrictSmallEtaleSheaf F z))
        (congrArg (fun a : X.p.obj x ⟶ X.p.obj z ↦ a.left) (X.p.map_comp φ ψ))) :
        (EtaleSheaf.pullback (X.p.map (φ ≫ ψ)).left).obj (restrictSmallEtaleSheaf F z) ⟶
          (EtaleSheaf.pullback ((X.p.map φ).left ≫ (X.p.map ψ).left)).obj
            (restrictSmallEtaleSheaf F z)) ≫
        (EtaleSheaf.pullbackComp (X.p.map ψ).left (X.p.map φ).left).inv.app
          (restrictSmallEtaleSheaf F z) ≫
        (EtaleSheaf.pullback (X.p.map φ).left).map (comparison ψ F) ≫
          comparison φ F)

variable [Etale (X.p.map φ).left]

/- Lemma 96.9.3 (2): If φ : x ⟶ y lies over an étale morphism of schemes
a : U ⟶ V, then comparison φ F is an isomorphism. -/
@[stacks 075D]
#check (AlgebraicGeometry.GroupoidsOver.comparison_isIso φ F : IsIso (comparison φ F))

end ComparisonComp

section RestrictionInverseImage

variable {Y : GroupoidsOver S} (f : Y ⟶ X) (y : Y.total)
variable (F : Sheaf X.etaleTopology (Type (u + 1)))
variable [HasSheafify Y.etaleTopology (Type (u + 1))]
variable [HasWeakSheafify Y.etaleTopology (Type (u + 1))]
variable [HasWeakSheafify X.etaleTopology (Type (u + 1))]
variable [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]

/- Lemma 96.9.3 (3): If f : Y ⟶ X is a 1-morphism of categories fibred in
groupoids and y lies over U with image x = f(y), there is a canonical
identification f⁻¹ F|_{U_étale} = F|_{U_étale}. -/
@[stacks 075D]
#check (AlgebraicGeometry.GroupoidsOver.restrictSmallEtaleSheaf_inverseImage f y F :
    restrictSmallEtaleSheaf
        (((toCartesianBasedFunctor f).morphismOfTopoiIn
            (StandardTopology.etale.overTopology S)).inverseImage.obj F)
        y ≅
      restrictSmallEtaleSheaf_reindex f y F)

end RestrictionInverseImage

section ComparisonInverseImage

variable {Y : GroupoidsOver S} (f : Y ⟶ X)
variable {y' y : Y.total} (ψY : y' ⟶ y)
variable (F : Sheaf X.etaleTopology (Type (u + 1)))
variable [HasSheafify Y.etaleTopology (Type (u + 1))]
variable [HasWeakSheafify Y.etaleTopology (Type (u + 1))]
variable [HasWeakSheafify X.etaleTopology (Type (u + 1))]
variable [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (Y.p.obj y').left.smallEtaleTopology (Type (u + 1))]
variable [∀ P : (Y.p.obj y).left.Etaleᵒᵖ ⥤ Type (u + 1),
    (smallEtalePullback (Y.p.map ψY).left).op.HasLeftKanExtension P]
variable [HasWeakSheafify (X.p.obj ((toFunctor f).obj y')).left.smallEtaleTopology
    (Type (u + 1))]
variable [∀ P : (X.p.obj ((toFunctor f).obj y)).left.Etaleᵒᵖ ⥤ Type (u + 1),
    (smallEtalePullback (X.p.map ((toFunctor f).map ψY)).left).op.HasLeftKanExtension P]

/- Lemma 96.9.3 (4): Given ψ : y' ⟶ y in Y lying over a : U' ⟶ U, the
comparison map c_ψ of f⁻¹ F equals the comparison map c_{f(ψ)} of F via the
identifications in (3). -/
@[stacks 075D]
#check (AlgebraicGeometry.GroupoidsOver.comparison_inverseImage f ψY F :
    comparison ψY
          (((toCartesianBasedFunctor f).morphismOfTopoiIn
              (StandardTopology.etale.overTopology S)).inverseImage.obj F) ≫
        (restrictSmallEtaleSheaf_inverseImage f y' F).hom =
      (EtaleSheaf.pullback (Y.p.map ψY).left).map
          (restrictSmallEtaleSheaf_inverseImage f y F).hom ≫
        restrictSmallEtaleSheaf_inverseImage_comp f ψY F)

end ComparisonInverseImage
