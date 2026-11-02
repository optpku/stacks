/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ModuleSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.InverseImage
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Functor CategoryTheory.Sheaf
open CategoryTheory.DerivedCategory ComplexShape

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.Etale.Kunneth

variable {P X Y S : Scheme.{u}} (Λ : Type u) [CommRing Λ]
variable [HasSheafify P.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.Etale,
  HasWeakSheafify (P.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory.{w} (Sheaf P.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory.{w} (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : S.Etale,
  HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory.{w} (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))]

variable (p : P ⟶ X) (q : P ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (c : P ⟶ S)
variable [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback p).op.HasLeftKanExtension F]
variable [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback q).op.HasLeftKanExtension F]
variable [∀ F : S.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ F : S.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g).op.HasLeftKanExtension F]
variable [∀ F : S.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback c).op.HasLeftKanExtension F]
variable [∀ F : S.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (p ≫ f)).op.HasLeftKanExtension F]
variable [∀ F : S.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (q ≫ g)).op.HasLeftKanExtension F]

/-- Composition of derived inverse images, obtained by localizing the canonical
sheaf adjunction comparison and transporting along the given equality of scheme morphisms. -/
def inverseImageComp (hc : c = p ≫ f) :
    etaleModuleDerivedInverseImage c Λ ≅
      etaleModuleDerivedInverseImage f Λ ⋙ etaleModuleDerivedInverseImage p Λ :=
  Functor.MapDerivedCategory.functorIso
      (Hom.etaleModuleSheafPullback_congr Λ hc ≪≫
        (Hom.etaleModuleSheafPullback_comp Λ f p).symm) ≪≫
    ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)))
      (ExactFunctor.of (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)))

/-- The two comparisons with `c⁻¹` recover the canonical inverse-image comparison
of the given cartesian square. -/
theorem inverseImageComp_square (hcart : IsPullback p q f g) (hc : c = p ≫ f) :
    (inverseImageComp Λ q g c (hc.trans hcart.w)).symm ≪≫ inverseImageComp Λ p f c hc =
      etaleModuleDerivedInverseImage_square f g q p hcart Λ := sorry

variable (adjP : ModuleDerivedAdjunction p Λ)
variable (adjF : ModuleDerivedAdjunction f Λ) (adjG : ModuleDerivedAdjunction g Λ)
variable (adjC : ModuleDerivedAdjunction c Λ)

/-- Direct-image composition is the adjunction mate of canonical inverse-image
composition.  In particular its normalization is fixed by the geometric sheaf functors. -/
def directImageComp (hc : c = p ≫ f) :
    etaleDerivedPushforward p (Λ := Λ) ⋙ etaleDerivedPushforward f (Λ := Λ) ≅ etaleDerivedPushforward c (Λ := Λ) :=
  conjugateIsoEquiv
    (adjF.val.comp
      adjP.val)
    adjC.val (inverseImageComp Λ p f c hc)

/-- The counit for `c` agrees with the composite counit under the canonical
inverse/direct-image composition comparisons. -/
theorem directImageComp_counit (hc : c = p ≫ f)
    (A : DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleModuleDerivedInverseImage c Λ).map ((directImageComp (Λ := Λ) (p := p) (f := f) (c := c)
          (adjP := adjP) (adjF := adjF) (adjC := adjC) hc).hom.app A) ≫
        adjC.val.counit.app A =
      (inverseImageComp Λ p f c hc).hom.app
          ((etaleDerivedPushforward f (Λ := Λ)).obj ((etaleDerivedPushforward p (Λ := Λ)).obj A)) ≫
        (etaleModuleDerivedInverseImage p Λ).map
          (adjF.val.counit.app
            ((etaleDerivedPushforward p (Λ := Λ)).obj A)) ≫
        adjP.val.counit.app A := sorry

/-- The canonical first edge map, transposed from inverse-image composition and the
counit of the derived adjunction for `f`. -/
def leftLeg (hc : c = p ≫ f)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleDerivedPushforward f (Λ := Λ)).obj E ⟶
      (etaleDerivedPushforward c (Λ := Λ)).obj ((etaleModuleDerivedInverseImage p Λ).obj E) :=
  adjC.val.homEquiv _ _
    ((inverseImageComp Λ p f c hc).hom.app ((etaleDerivedPushforward f (Λ := Λ)).obj E) ≫
      (etaleModuleDerivedInverseImage p Λ).map
        (adjF.val.counit.app E))

/-- The edge map is also obtained from the geometric inverse-image unit and
canonical direct-image composition. -/
theorem leftLeg_eq_unit (hc : c = p ≫ f)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    leftLeg Λ p f c adjF adjC hc E =
      (etaleDerivedPushforward f (Λ := Λ)).map
          (adjP.val.unit.app E) ≫
        (directImageComp (Λ := Λ) (p := p) (f := f) (c := c)
          (adjP := adjP) (adjF := adjF) (adjC := adjC) hc).hom.app
          ((etaleModuleDerivedInverseImage p Λ).obj E) := sorry

/-- The canonical second edge map. -/
def rightLeg (hc : c = q ≫ g)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleDerivedPushforward g (Λ := Λ)).obj K ⟶
      (etaleDerivedPushforward c (Λ := Λ)).obj ((etaleModuleDerivedInverseImage q Λ).obj K) :=
  leftLeg Λ q g c adjG adjC hc K

/-- The first edge is the mate of the composite of the canonical composition comparison
and the canonical counit.  This fixes its compatibility with the adjunction for `c`. -/
theorem leftLeg_counit (hc : c = p ≫ f)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleModuleDerivedInverseImage c Λ).map (leftLeg Λ p f c adjF adjC hc E) ≫
        adjC.val.counit.app
          ((etaleModuleDerivedInverseImage p Λ).obj E) =
      (inverseImageComp Λ p f c hc).hom.app ((etaleDerivedPushforward f (Λ := Λ)).obj E) ≫
        (etaleModuleDerivedInverseImage p Λ).map
          (adjF.val.counit.app E) := by
  exact (adjC.val.homEquiv _ _).symm_apply_apply _

/-- The second edge has the same canonical counit compatibility. -/
theorem rightLeg_counit (hc : c = q ≫ g)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleModuleDerivedInverseImage c Λ).map (rightLeg Λ q g c adjG adjC hc K) ≫
        adjC.val.counit.app
          ((etaleModuleDerivedInverseImage q Λ).obj K) =
      (inverseImageComp Λ q g c hc).hom.app ((etaleDerivedPushforward g (Λ := Λ)).obj K) ≫
        (etaleModuleDerivedInverseImage q Λ).map
          (adjG.val.counit.app K) :=
  leftLeg_counit Λ q g c adjG adjC hc K

variable [(P.smallEtaleTopology.W (A := ModuleCat.{u} Λ)).IsMonoidal]
variable [MonoidalPreadditive (Sheaf P.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ G₁ G₂ : GradedObject ℤ (Sheaf P.smallEtaleTopology (ModuleCat.{u} Λ)), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf P.smallEtaleTopology (ModuleCat.{u} Λ)),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf P.smallEtaleTopology (ModuleCat.{u} Λ)),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (Sheaf P.smallEtaleTopology (ModuleCat.{u} Λ)),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := (Sheaf P.smallEtaleTopology (ModuleCat.{u} Λ)))]
variable [DerivedTensor.Bifunctor.Has (C := (Sheaf P.smallEtaleTopology (ModuleCat.{u} Λ)))]
variable [(S.smallEtaleTopology.W (A := ModuleCat.{u} Λ)).IsMonoidal]
variable [MonoidalPreadditive (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ G₁ G₂ : GradedObject ℤ (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)))]
variable [DerivedTensor.Bifunctor.Has (C := (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)))]

/-- The relative cup product for a normalized two-variable derived tensor comparison
induced by the actual inverse image of module sheaves along `c`. -/
def relativeCupProduct
    (comparison : moduleDerivedInverseImageTensorComparison c Λ)
    (hcomparison : moduleDerivedInverseImageTensorIsNormalized c Λ comparison)
    (A B : DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u} Λ))) :
    DerivedTensor.Bifunctor.obj ((etaleDerivedPushforward c (Λ := Λ)).obj A)
        ((etaleDerivedPushforward c (Λ := Λ)).obj B) ⟶
      (etaleDerivedPushforward c (Λ := Λ)).obj (DerivedTensor.Bifunctor.obj A B) :=
  adjC.val.homEquiv _ _
    (moduleDerivedInverseImageTensorHom c Λ comparison _ _ ≫
      DerivedTensor.Bifunctor.functor.map
        (adjC.val.counit.app A,
          adjC.val.counit.app B))

/-- The adjoint-side Künneth map: the canonical tensor comparison followed by inverse
images of the counits for `f` and `g`.  The second composition equality is supplied by the
cartesian square, so its inverse-image comparison is attached to that square. -/
def adjointMap
    (comparison : moduleDerivedInverseImageTensorComparison c Λ)
    (hcomparison : moduleDerivedInverseImageTensorIsNormalized c Λ comparison)
    (hcart : IsPullback p q f g) (hc : c = p ≫ f)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleModuleDerivedInverseImage c Λ).obj
        (DerivedTensor.Bifunctor.obj ((etaleDerivedPushforward f (Λ := Λ)).obj E)
          ((etaleDerivedPushforward g (Λ := Λ)).obj K)) ⟶
      DerivedTensor.Bifunctor.obj ((etaleModuleDerivedInverseImage p Λ).obj E)
        ((etaleModuleDerivedInverseImage q Λ).obj K) :=
  moduleDerivedInverseImageTensorHom c Λ comparison _ _ ≫
    DerivedTensor.Bifunctor.functor.map
      ((inverseImageComp Λ p f c hc).hom.app ((etaleDerivedPushforward f (Λ := Λ)).obj E) ≫
          (etaleModuleDerivedInverseImage p Λ).map
            (adjF.val.counit.app E),
        (inverseImageComp Λ q g c (hc.trans hcart.w)).hom.app
            ((etaleDerivedPushforward g (Λ := Λ)).obj K) ≫
          (etaleModuleDerivedInverseImage q Λ).map
            (adjG.val.counit.app K))

/-- The canonical Künneth morphism for a cartesian square of schemes, with arbitrary
commutative coefficients.  The functors are the small-étale derived constructions.  The supplied adjunctions and
tensor comparison are normalized against the concrete geometric constructions on complexes. -/
def map
    (comparison : moduleDerivedInverseImageTensorComparison c Λ)
    (hcomparison : moduleDerivedInverseImageTensorIsNormalized c Λ comparison)
    (hcart : IsPullback p q f g) (hc : c = p ≫ f)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :
    DerivedTensor.Bifunctor.obj ((etaleDerivedPushforward f (Λ := Λ)).obj E)
        ((etaleDerivedPushforward g (Λ := Λ)).obj K) ⟶
      (etaleDerivedPushforward c (Λ := Λ)).obj
        (DerivedTensor.Bifunctor.obj ((etaleModuleDerivedInverseImage p Λ).obj E)
          ((etaleModuleDerivedInverseImage q Λ).obj K)) :=
  adjC.val.homEquiv _ _
    (adjointMap (Λ := Λ) (p := p) (q := q) (f := f) (g := g) (c := c)
      (adjF := adjF) (adjG := adjG) comparison hcomparison hcart hc E K)

/-- The canonical map also factors through the two canonical edge maps and the relative
cup product, as in Stacks 0F1E. -/
theorem map_eq
    (comparison : moduleDerivedInverseImageTensorComparison c Λ)
    (hcomparison : moduleDerivedInverseImageTensorIsNormalized c Λ comparison)
    (hcart : IsPullback p q f g) (hc : c = p ≫ f)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :
    map (Λ := Λ) (p := p) (q := q) (f := f) (g := g) (c := c)
      (adjF := adjF) (adjG := adjG) (adjC := adjC) comparison hcomparison hcart hc E K =
      DerivedTensor.Bifunctor.functor.map
          (leftLeg Λ p f c adjF adjC hc E, rightLeg Λ q g c adjG adjC (hc.trans hcart.w) K) ≫
        relativeCupProduct Λ c adjC comparison hcomparison ((etaleModuleDerivedInverseImage p Λ).obj E)
          ((etaleModuleDerivedInverseImage q Λ).obj K) := sorry

/-- Transposing the canonical Künneth map recovers its defining adjoint-side composite. -/
theorem map_adjoint_spec
    (comparison : moduleDerivedInverseImageTensorComparison c Λ)
    (hcomparison : moduleDerivedInverseImageTensorIsNormalized c Λ comparison)
    (hcart : IsPullback p q f g) (hc : c = p ≫ f)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (adjC.val.homEquiv _ _).symm
        (map (Λ := Λ) (p := p) (q := q) (f := f) (g := g) (c := c)
      (adjF := adjF) (adjG := adjG) (adjC := adjC) comparison hcomparison hcart hc E K) =
      adjointMap (Λ := Λ) (p := p) (q := q) (f := f) (g := g) (c := c)
      (adjF := adjF) (adjG := adjG) comparison hcomparison hcart hc E K :=
  (adjC.val.homEquiv _ _).symm_apply_apply _

end AlgebraicGeometry.Scheme.Etale.Kunneth
