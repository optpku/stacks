/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Universe
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ZMod
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Coefficients
public import ReasLib.CategoryTheory.Adjunction.FullyFaithful

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Sheaf CategoryTheory.DerivedCategory
open CategoryTheory.Adjunction.Derived ComplexShape

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.Etale

variable {A B : Scheme.{u}} (p : A ⟶ B) (n : ℕ)
variable [(A.smallEtaleTopology.W (A := ModuleCat.{u} (ZMod n))).IsMonoidal]
variable [(B.smallEtaleTopology.W (A := ModuleCat.{u} (ZMod n))).IsMonoidal]

/-- Direct image carries a canonical tensor comparison induced by restriction of
presheaves and the universal map of sheafification. -/
def zmodSheafPushforwardTensorHom
    (F G : Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n))) :
    (zmodSheafPushforward p n).obj F ⊗ (zmodSheafPushforward p n).obj G ⟶
      (zmodSheafPushforward p n).obj (F ⊗ G) :=
  let adj := sheafificationAdjunction B.smallEtaleTopology (ModuleCat.{u} (ZMod n))
  let R := zmodSheafPushforward p n
  let counitIso := adj.counitIsoOfRFullyFaithful
    (fullyFaithfulSheafToPresheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n)))
  ((tensorIso (counitIso.app (R.obj F)).symm
      (counitIso.app (R.obj G)).symm) ≪≫
    Functor.Monoidal.μIso (presheafToSheaf B.smallEtaleTopology
      (ModuleCat.{u} (ZMod n))) (R.obj F).obj (R.obj G).obj).hom ≫
    ((sheafificationAdjunction B.smallEtaleTopology (ModuleCat.{u} (ZMod n))).homEquiv
      _ _).symm
      ((Functor.Monoidal.μIso
          ((Functor.whiskeringLeft _ _ (ModuleCat.{u} (ZMod n))).obj
            (smallEtalePullback p).op) F.obj G.obj).hom ≫
        Functor.whiskerLeft (smallEtalePullback p).op
          (((sheafificationAdjunction A.smallEtaleTopology
            (ModuleCat.{u} (ZMod n))).rightAdjointLaxMonoidal).μ F G))

/-- The direct-image tensor comparison is natural in both sheaves. -/
theorem zmodSheafPushforwardTensorHom_naturality
    {F F' G G' : Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n))}
    (f : F ⟶ F') (g : G ⟶ G') :
    ((zmodSheafPushforward p n).map f ⊗ₘ (zmodSheafPushforward p n).map g) ≫
        zmodSheafPushforwardTensorHom p n F' G' =
      zmodSheafPushforwardTensorHom p n F G ≫
        (zmodSheafPushforward p n).map (f ⊗ₘ g) := sorry

/-- The inverse-image tensor comparison is the adjunction mate of the direct-image
comparison composed with the two adjunction units. -/
def zmodSheafPullbackTensorHom
    (F G : Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))) :
    (zmodSheafPullback p n).obj (F ⊗ G) ⟶
      (zmodSheafPullback p n).obj F ⊗ (zmodSheafPullback p n).obj G :=
  ((zmodSheafAdjunction p n).homEquiv _ _).symm
    (((zmodSheafAdjunction p n).unit.app F ⊗ₘ
        (zmodSheafAdjunction p n).unit.app G) ≫
      zmodSheafPushforwardTensorHom p n
        ((zmodSheafPullback p n).obj F) ((zmodSheafPullback p n).obj G))

/-- The inverse-image tensor comparison is natural in both sheaves. -/
theorem zmodSheafPullbackTensorHom_naturality
    {F F' G G' : Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))}
    (f : F ⟶ F') (g : G ⟶ G') :
    (zmodSheafPullback p n).map (f ⊗ₘ g) ≫ zmodSheafPullbackTensorHom p n F' G' =
      zmodSheafPullbackTensorHom p n F G ≫
        ((zmodSheafPullback p n).map f ⊗ₘ (zmodSheafPullback p n).map g) := sorry

variable [MonoidalPreadditive (Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [MonoidalPreadditive (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [∀ G₁ G₂ : GradedObject ℤ
    (Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n))), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ : GradedObject ℤ
    (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))), GradedObject.HasTensor G₁ G₂]

/-- On each degree of a total tensor complex, inverse image is compared with the
tensor of inverse images by adjunction and the coproduct inclusions. -/
def zmodPullbackComplexTensorHomComponent
    (K L : CochainComplex (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))) ℤ)
    (j : ℤ) :
    (zmodSheafPullback p n).obj ((HomologicalComplex.tensorObj K L).X j) ⟶
      (HomologicalComplex.tensorObj
        ((zmodSheafPullback p n).mapHomologicalComplex (up ℤ) |>.obj K)
        ((zmodSheafPullback p n).mapHomologicalComplex (up ℤ) |>.obj L)).X j :=
  ((zmodSheafAdjunction p n).homEquiv _ _).symm
    (HomologicalComplex.mapBifunctorDesc (fun i₁ i₂ hij =>
      (((zmodSheafAdjunction p n).unit.app (K.X i₁) ⊗ₘ
        (zmodSheafAdjunction p n).unit.app (L.X i₂)) ≫
        zmodSheafPushforwardTensorHom p n
          ((zmodSheafPullback p n).obj (K.X i₁))
          ((zmodSheafPullback p n).obj (L.X i₂))) ≫
        (zmodSheafPushforward p n).map
          (HomologicalComplex.ιTensorObj
            ((zmodSheafPullback p n).mapHomologicalComplex (up ℤ) |>.obj K)
            ((zmodSheafPullback p n).mapHomologicalComplex (up ℤ) |>.obj L)
            i₁ i₂ j hij)))

/-- The degreewise inverse-image tensor comparison commutes with the total
differential, including the cochain signs. -/
theorem zmodPullbackComplexTensorHom_comm
    (K L : CochainComplex (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))) ℤ)
    (i j : ℤ) :
    (zmodSheafPullback p n).map ((HomologicalComplex.tensorObj K L).d i j) ≫
        zmodPullbackComplexTensorHomComponent p n K L j =
      zmodPullbackComplexTensorHomComponent p n K L i ≫
        (HomologicalComplex.tensorObj
          ((zmodSheafPullback p n).mapHomologicalComplex (up ℤ) |>.obj K)
          ((zmodSheafPullback p n).mapHomologicalComplex (up ℤ) |>.obj L)).d i j := sorry

/-- The tensor comparison of inverse image on cochain complexes has the canonical
adjunction-mate maps in each degree. -/
def zmodPullbackComplexTensorHom
    (K L : CochainComplex (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))) ℤ) :
    ((zmodSheafPullback p n).mapHomologicalComplex (up ℤ)).obj
        (HomologicalComplex.tensorObj K L) ⟶
      HomologicalComplex.tensorObj
        ((zmodSheafPullback p n).mapHomologicalComplex (up ℤ) |>.obj K)
        ((zmodSheafPullback p n).mapHomologicalComplex (up ℤ) |>.obj L) where
  f j := zmodPullbackComplexTensorHomComponent p n K L j
  comm' i j _ := (zmodPullbackComplexTensorHom_comm p n K L i j).symm

/-- The cochain inverse-image tensor comparison is natural in both complexes. -/
theorem zmodPullbackComplexTensorHom_naturality
    {K K' L L' : CochainComplex (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') :
    ((zmodSheafPullback p n).mapHomologicalComplex (up ℤ)).map
        (HomologicalComplex.tensorHom f g) ≫ zmodPullbackComplexTensorHom p n K' L' =
      zmodPullbackComplexTensorHom p n K L ≫ HomologicalComplex.tensorHom
        (((zmodSheafPullback p n).mapHomologicalComplex (up ℤ)).map f)
        (((zmodSheafPullback p n).mapHomologicalComplex (up ℤ)).map g) := sorry

variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n))),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n))),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n))),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := (Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n))))]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))))]

variable [HasDerivedCategory.{w} (Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [HasDerivedCategory.{w} (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]

/-- Inverse image of the ordinary totalized homotopy tensor, localized in the target. -/
abbrev zmodInverseImageTensorSource :
    HomotopyCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))) (up ℤ) ×
      HomotopyCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))) (up ℤ) ⥤
      DerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n))) :=
  tensor _ ⋙ (zmodSheafPullback p n).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The ordinary homotopy tensor after applying inverse image in both variables,
localized in the target. -/
abbrev zmodInverseImageTensorTarget :
    HomotopyCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))) (up ℤ) ×
      HomotopyCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))) (up ℤ) ⥤
      DerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n))) :=
  ((zmodSheafPullback p n).mapHomotopyCategory (up ℤ)).prod
    ((zmodSheafPullback p n).mapHomotopyCategory (up ℤ)) ⋙ tensor _ ⋙ DerivedCategory.Qh

/-- The inverse-image tensor comparison on homotopy objects is the localization
descent of the concrete comparison of total complexes. -/
def zmodPullbackHomotopyTensorHom :
    zmodInverseImageTensorSource p n ⟶ zmodInverseImageTensorTarget p n :=
  let C := Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))
  let D := Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n))
  let qC := HomotopyCategory.quotient C (up ℤ)
  let qD := HomotopyCategory.quotient D (up ℤ)
  let L := (zmodSheafPullback p n).mapHomologicalComplex (up ℤ)
  let P := (zmodSheafPullback p n).mapHomotopyCategory (up ℤ)
  let QD := (DerivedCategory.Q : CochainComplex D ℤ ⥤ DerivedCategory D)
  let QhD := (DerivedCategory.Qh : HomotopyCategory D (up ℤ) ⥤ DerivedCategory D)
  let ε := (zmodSheafPullback p n).mapHomotopyCategoryFactors (up ℤ)
  let sourceIso :
      qC.prod qC ⋙ zmodInverseImageTensorSource p n ≅ tensor _ ⋙ L ⋙ QD :=
    Functor.isoWhiskerRight (Functor.Monoidal.μNatIso qC) (P ⋙ QhD) ≪≫
      Functor.isoWhiskerLeft (tensor _)
        (Functor.isoWhiskerRight ε QhD ≪≫
          Functor.isoWhiskerLeft L (DerivedCategory.quotientCompQhIso D))
  let targetIso :
      qC.prod qC ⋙ zmodInverseImageTensorTarget p n ≅ L.prod L ⋙ tensor _ ⋙ QD :=
    Functor.isoWhiskerRight (NatIso.prod ε ε) (tensor _ ⋙ QhD) ≪≫
      Functor.isoWhiskerLeft (L.prod L)
        (Functor.isoWhiskerRight (Functor.Monoidal.μNatIso qD) QhD ≪≫
          Functor.isoWhiskerLeft (tensor _) (DerivedCategory.quotientCompQhIso D))
  let τ : tensor _ ⋙ L ⋙ QD ⟶ L.prod L ⋙ tensor _ ⋙ QD :=
    { app K := QD.map (zmodPullbackComplexTensorHom p n K.1 K.2)
      naturality K L f := by
        change QD.map _ ≫ QD.map _ = QD.map _ ≫ QD.map _
        rw [← QD.map_comp, ← QD.map_comp]
        exact congrArg QD.map (zmodPullbackComplexTensorHom_naturality p n f.1 f.2) }
  Localization.liftNatTrans (qC.prod qC)
    ((HomologicalComplex.homotopyEquivalences C (up ℤ)).prod
      (HomologicalComplex.homotopyEquivalences C (up ℤ)))
    _ _ (zmodInverseImageTensorSource p n) (zmodInverseImageTensorTarget p n)
    (sourceIso.hom ≫ τ ≫ targetIso.inv)

variable [DerivedTensor.Bifunctor.Has
    (C := Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [DerivedTensor.Bifunctor.Has
    (C := Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]

/-- The source iterated model counit first compares derived and homotopy tensor,
then applies the exact inverse-image localization factor. -/
def zmodDerivedInverseImageTensorSourceCounit :
    DerivedTensor.Bifunctor.localization ⋙
        (DerivedTensor.Bifunctor.functor ⋙ zmodDerivedInverseImage p n) ⟶
      zmodInverseImageTensorSource p n :=
  Functor.whiskerRight
      (DerivedTensor.Bifunctor.counit ≫ DerivedTensor.Bifunctor.sourceFunctorIso.inv)
      (zmodDerivedInverseImage p n) ≫
    Functor.whiskerLeft (tensor _)
      (zmodPullbackExact p n).obj.mapDerivedCategoryFactorsh.hom

/-- The target iterated model counit uses the exact inverse-image factor in each
variable, followed by the canonical two-variable derived-tensor counit. -/
def zmodDerivedInverseImageTensorTargetCounit :
    DerivedTensor.Bifunctor.localization ⋙
        ((zmodDerivedInverseImage p n).prod (zmodDerivedInverseImage p n) ⋙
          DerivedTensor.Bifunctor.functor) ⟶
      zmodInverseImageTensorTarget p n :=
  Functor.whiskerRight
      (NatTrans.prod (zmodPullbackExact p n).obj.mapDerivedCategoryFactorsh.hom
        (zmodPullbackExact p n).obj.mapDerivedCategoryFactorsh.hom)
      DerivedTensor.Bifunctor.functor ≫
    Functor.whiskerLeft
      (((zmodSheafPullback p n).mapHomotopyCategory (up ℤ)).prod
        ((zmodSheafPullback p n).mapHomotopyCategory (up ℤ)))
      (DerivedTensor.Bifunctor.counit ≫ DerivedTensor.Bifunctor.sourceFunctorIso.inv)

/-- The tensor of the two exact inverse images, with its canonical counit,
is the left-derived model of the ordinary inverse-image tensor. -/
instance zmodDerivedInverseImageTensorTarget_isLeftDerived :
    ((zmodDerivedInverseImage p n).prod (zmodDerivedInverseImage p n) ⋙
      DerivedTensor.Bifunctor.functor).IsLeftDerivedFunctor
        (zmodDerivedInverseImageTensorTargetCounit p n) DerivedTensor.Bifunctor.qis := sorry

/-- The derived inverse-image tensor comparison is induced by the concrete
homotopy comparison using the target left-derived universal property. -/
def zmodDerivedInverseImageTensorNatTrans :
    DerivedTensor.Bifunctor.functor ⋙ zmodDerivedInverseImage p n ⟶
      (zmodDerivedInverseImage p n).prod (zmodDerivedInverseImage p n) ⋙
        DerivedTensor.Bifunctor.functor :=
  Functor.leftDerivedNatTrans _ _
    (zmodDerivedInverseImageTensorSourceCounit p n)
    (zmodDerivedInverseImageTensorTargetCounit p n)
    DerivedTensor.Bifunctor.qis (zmodPullbackHomotopyTensorHom p n)

/-- The derived inverse-image tensor comparison identifies the canonical source
and target counits through the ordinary tensor comparison. -/
theorem zmodDerivedInverseImageTensorNatTrans_counit :
    Functor.whiskerLeft DerivedTensor.Bifunctor.localization
        (zmodDerivedInverseImageTensorNatTrans p n) ≫
      zmodDerivedInverseImageTensorTargetCounit p n =
    zmodDerivedInverseImageTensorSourceCounit p n ≫ zmodPullbackHomotopyTensorHom p n :=
  Functor.leftDerivedNatTrans_fac _ _ _ _ _ _

/-- The component of the canonical derived inverse-image tensor comparison. -/
def zmodDerivedInverseImageTensorHom
    (K L : DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    (zmodDerivedInverseImage p n).obj (DerivedTensor.Bifunctor.obj K L) ⟶
      DerivedTensor.Bifunctor.obj
        ((zmodDerivedInverseImage p n).obj K) ((zmodDerivedInverseImage p n).obj L) :=
  (zmodDerivedInverseImageTensorNatTrans p n).app (K, L)


section GeneralCoefficients

/-! The same construction for any commutative coefficient ring.  Its normalization is fixed
at the sheaf level by the sheafification adjunction and sectionwise tensor, then transported through cochain totalization
and the two-variable derived-tensor counits.  A supplied comparison carries an explicit
normalization witness; no data are selected from an admitted existence theorem. -/

variable {A B : Scheme.{u}} (p : A ⟶ B) (Λ : Type u) [CommRing Λ]
variable [HasSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify B.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ V : A.Etale, HasWeakSheafify (A.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [∀ V : B.Etale, HasWeakSheafify (B.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [∀ F : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback p).op.HasLeftKanExtension F]
variable [(A.smallEtaleTopology.W (A := ModuleCat.{u} Λ)).IsMonoidal]
variable [(B.smallEtaleTopology.W (A := ModuleCat.{u} Λ)).IsMonoidal]

/-- Direct image carries a canonical tensor comparison induced by restriction of
presheaves and the universal map of sheafification. -/
def moduleTensorPushforward
    (F G : Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (etaleModulePushforward p Λ).obj F ⊗ (etaleModulePushforward p Λ).obj G ⟶
      (etaleModulePushforward p Λ).obj (F ⊗ G) :=
  let adj := sheafificationAdjunction B.smallEtaleTopology (ModuleCat.{u} Λ)
  let R := etaleModulePushforward p Λ
  let counitIso := adj.counitIsoOfRFullyFaithful
    (fullyFaithfulSheafToPresheaf B.smallEtaleTopology (ModuleCat.{u} Λ))
  ((tensorIso (counitIso.app (R.obj F)).symm
      (counitIso.app (R.obj G)).symm) ≪≫
    Functor.Monoidal.μIso (presheafToSheaf B.smallEtaleTopology
      (ModuleCat.{u} Λ)) (R.obj F).obj (R.obj G).obj).hom ≫
    ((sheafificationAdjunction B.smallEtaleTopology (ModuleCat.{u} Λ)).homEquiv
      _ _).symm
      ((Functor.Monoidal.μIso
          ((Functor.whiskeringLeft _ _ (ModuleCat.{u} Λ)).obj
            (smallEtalePullback p).op) F.obj G.obj).hom ≫
        Functor.whiskerLeft (smallEtalePullback p).op
          (((sheafificationAdjunction A.smallEtaleTopology
            (ModuleCat.{u} Λ)).rightAdjointLaxMonoidal).μ F G))

/-- The inverse-image tensor comparison is the adjunction mate of the direct-image
comparison composed with the two adjunction units. -/
def moduleSheafPullbackTensorHom
    (F G : Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).obj (F ⊗ G) ⟶
      (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).obj F ⊗ (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).obj G :=
  (((smallEtalePullback p).sheafAdjunctionContinuous (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology).homEquiv _ _).symm
    ((((smallEtalePullback p).sheafAdjunctionContinuous (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology).unit.app F ⊗ₘ
        ((smallEtalePullback p).sheafAdjunctionContinuous (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology).unit.app G) ≫
      moduleTensorPushforward p Λ
        ((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).obj F) ((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).obj G))

/-- The inverse-image tensor comparison is natural in both sheaves. -/
theorem moduleSheafPullbackTensorHom_naturality
    {F F' G G' : Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ)}
    (f : F ⟶ F') (g : G ⟶ G') :
    (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).map (f ⊗ₘ g) ≫ moduleSheafPullbackTensorHom p Λ F' G' =
      moduleSheafPullbackTensorHom p Λ F G ≫
        ((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).map f ⊗ₘ (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).map g) := sorry

variable [MonoidalPreadditive (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [MonoidalPreadditive (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ G₁ G₂ : GradedObject ℤ
    (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ)), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ : GradedObject ℤ
    (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ)), GradedObject.HasTensor G₁ G₂]

/-- On each degree of a total tensor complex, inverse image is compared with the
tensor of inverse images by adjunction and the coproduct inclusions. -/
def modulePullbackComplexTensorHomComponent
    (K L : CochainComplex (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ)
    (j : ℤ) :
    (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).obj ((HomologicalComplex.tensorObj K L).X j) ⟶
      (HomologicalComplex.tensorObj
        ((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomologicalComplex (up ℤ) |>.obj K)
        ((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomologicalComplex (up ℤ) |>.obj L)).X j :=
  (((smallEtalePullback p).sheafAdjunctionContinuous (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology).homEquiv _ _).symm
    (HomologicalComplex.mapBifunctorDesc (fun i₁ i₂ hij =>
      ((((smallEtalePullback p).sheafAdjunctionContinuous (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology).unit.app (K.X i₁) ⊗ₘ
        ((smallEtalePullback p).sheafAdjunctionContinuous (ModuleCat.{u} Λ) B.smallEtaleTopology A.smallEtaleTopology).unit.app (L.X i₂)) ≫
        moduleTensorPushforward p Λ
          ((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).obj (K.X i₁))
          ((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).obj (L.X i₂))) ≫
        (etaleModulePushforward p Λ).map
          (HomologicalComplex.ιTensorObj
            ((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomologicalComplex (up ℤ) |>.obj K)
            ((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomologicalComplex (up ℤ) |>.obj L)
            i₁ i₂ j hij)))

/-- The degreewise inverse-image tensor comparison commutes with the total
differential, including the cochain signs. -/
theorem modulePullbackComplexTensorHom_comm
    (K L : CochainComplex (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ)
    (i j : ℤ) :
    (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).map ((HomologicalComplex.tensorObj K L).d i j) ≫
        modulePullbackComplexTensorHomComponent p Λ K L j =
      modulePullbackComplexTensorHomComponent p Λ K L i ≫
        (HomologicalComplex.tensorObj
          ((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomologicalComplex (up ℤ) |>.obj K)
          ((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomologicalComplex (up ℤ) |>.obj L)).d i j := sorry

/-- The tensor comparison of inverse image on cochain complexes has the canonical
adjunction-mate maps in each degree. -/
def modulePullbackComplexTensorHom
    (K L : CochainComplex (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ) :
    ((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomologicalComplex (up ℤ)).obj
        (HomologicalComplex.tensorObj K L) ⟶
      HomologicalComplex.tensorObj
        ((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomologicalComplex (up ℤ) |>.obj K)
        ((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomologicalComplex (up ℤ) |>.obj L) where
  f j := modulePullbackComplexTensorHomComponent p Λ K L j
  comm' i j _ := (modulePullbackComplexTensorHom_comm p Λ K L i j).symm

/-- The cochain inverse-image tensor comparison is natural in both complexes. -/
theorem modulePullbackComplexTensorHom_naturality
    {K K' L L' : CochainComplex (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') :
    ((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomologicalComplex (up ℤ)).map
        (HomologicalComplex.tensorHom f g) ≫ modulePullbackComplexTensorHom p Λ K' L' =
      modulePullbackComplexTensorHom p Λ K L ≫ HomologicalComplex.tensorHom
        (((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomologicalComplex (up ℤ)).map f)
        (((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomologicalComplex (up ℤ)).map g) := sorry

variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ)),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ)),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ)),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ)))]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ)),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ)),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ)),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ)))]

variable [HasDerivedCategory.{w} (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory.{w} (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Inverse image of the ordinary totalized homotopy tensor, localized in the target. -/
abbrev moduleInverseImageTensorSource :
    HomotopyCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ) ×
      HomotopyCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ) ⥤
      DerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  tensor _ ⋙ (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The ordinary homotopy tensor after applying inverse image in both variables,
localized in the target. -/
abbrev moduleInverseImageTensorTarget :
    HomotopyCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ) ×
      HomotopyCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ) ⥤
      DerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  ((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomotopyCategory (up ℤ)).prod
    ((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomotopyCategory (up ℤ)) ⋙ tensor _ ⋙ DerivedCategory.Qh

/-- The inverse-image tensor comparison on homotopy objects is the localization
descent of the concrete comparison of total complexes. -/
def modulePullbackHomotopyTensorHom :
    moduleInverseImageTensorSource p Λ ⟶ moduleInverseImageTensorTarget p Λ :=
  let C := Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ)
  let D := Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ)
  let qC := HomotopyCategory.quotient C (up ℤ)
  let qD := HomotopyCategory.quotient D (up ℤ)
  let L := (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomologicalComplex (up ℤ)
  let P := (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomotopyCategory (up ℤ)
  let QD := (DerivedCategory.Q : CochainComplex D ℤ ⥤ DerivedCategory D)
  let QhD := (DerivedCategory.Qh : HomotopyCategory D (up ℤ) ⥤ DerivedCategory D)
  let ε := (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomotopyCategoryFactors (up ℤ)
  let sourceIso :
      qC.prod qC ⋙ moduleInverseImageTensorSource p Λ ≅ tensor _ ⋙ L ⋙ QD :=
    Functor.isoWhiskerRight (Functor.Monoidal.μNatIso qC) (P ⋙ QhD) ≪≫
      Functor.isoWhiskerLeft (tensor _)
        (Functor.isoWhiskerRight ε QhD ≪≫
          Functor.isoWhiskerLeft L (DerivedCategory.quotientCompQhIso D))
  let targetIso :
      qC.prod qC ⋙ moduleInverseImageTensorTarget p Λ ≅ L.prod L ⋙ tensor _ ⋙ QD :=
    Functor.isoWhiskerRight (NatIso.prod ε ε) (tensor _ ⋙ QhD) ≪≫
      Functor.isoWhiskerLeft (L.prod L)
        (Functor.isoWhiskerRight (Functor.Monoidal.μNatIso qD) QhD ≪≫
          Functor.isoWhiskerLeft (tensor _) (DerivedCategory.quotientCompQhIso D))
  let τ : tensor _ ⋙ L ⋙ QD ⟶ L.prod L ⋙ tensor _ ⋙ QD :=
    { app K := QD.map (modulePullbackComplexTensorHom p Λ K.1 K.2)
      naturality K L f := by
        change QD.map _ ≫ QD.map _ = QD.map _ ≫ QD.map _
        rw [← QD.map_comp, ← QD.map_comp]
        exact congrArg QD.map (modulePullbackComplexTensorHom_naturality p Λ f.1 f.2) }
  Localization.liftNatTrans (qC.prod qC)
    ((HomologicalComplex.homotopyEquivalences C (up ℤ)).prod
      (HomologicalComplex.homotopyEquivalences C (up ℤ)))
    _ _ (moduleInverseImageTensorSource p Λ) (moduleInverseImageTensorTarget p Λ)
    (sourceIso.hom ≫ τ ≫ targetIso.inv)

variable [DerivedTensor.Bifunctor.Has
    (C := Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [DerivedTensor.Bifunctor.Has
    (C := Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- The source iterated model counit first compares derived and homotopy tensor,
then applies the exact inverse-image localization factor. -/
def moduleDerivedInverseImageTensorSourceCounit :
    DerivedTensor.Bifunctor.localization ⋙
        (DerivedTensor.Bifunctor.functor ⋙ etaleModuleDerivedInverseImage p Λ) ⟶
      moduleInverseImageTensorSource p Λ :=
  Functor.whiskerRight
      (DerivedTensor.Bifunctor.counit ≫ DerivedTensor.Bifunctor.sourceFunctorIso.inv)
      (etaleModuleDerivedInverseImage p Λ) ≫
    Functor.whiskerLeft (tensor _)
      (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapDerivedCategoryFactorsh.hom

/-- The target iterated model counit uses the exact inverse-image factor in each
variable, followed by the canonical two-variable derived-tensor counit. -/
def moduleDerivedInverseImageTensorTargetCounit :
    DerivedTensor.Bifunctor.localization ⋙
        ((etaleModuleDerivedInverseImage p Λ).prod (etaleModuleDerivedInverseImage p Λ) ⋙
          DerivedTensor.Bifunctor.functor) ⟶
      moduleInverseImageTensorTarget p Λ :=
  Functor.whiskerRight
      (NatTrans.prod (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapDerivedCategoryFactorsh.hom
        (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapDerivedCategoryFactorsh.hom)
      DerivedTensor.Bifunctor.functor ≫
    Functor.whiskerLeft
      (((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomotopyCategory (up ℤ)).prod
        ((Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ)).mapHomotopyCategory (up ℤ)))
      (DerivedTensor.Bifunctor.counit ≫ DerivedTensor.Bifunctor.sourceFunctorIso.inv)

/-- The type of functorial derived inverse-image tensor comparisons.  Supplying such a
natural transformation is data; `moduleDerivedInverseImageTensorIsNormalized` separately
specifies its canonical normalization. -/
abbrev moduleDerivedInverseImageTensorComparison :=
  DerivedTensor.Bifunctor.functor ⋙ etaleModuleDerivedInverseImage p Λ ⟶
    (etaleModuleDerivedInverseImage p Λ).prod (etaleModuleDerivedInverseImage p Λ) ⋙
      DerivedTensor.Bifunctor.functor

/-- A chosen comparison must induce the concrete total-complex tensor comparison through
the canonical derived-tensor counits and exact inverse-image localization factors.
This fixes the comparison, rather than merely imposing naturality on an arbitrary family. -/
abbrev moduleDerivedInverseImageTensorIsNormalized
    (comparison : moduleDerivedInverseImageTensorComparison p Λ) : Prop :=
  Functor.whiskerLeft DerivedTensor.Bifunctor.localization comparison ≫
      moduleDerivedInverseImageTensorTargetCounit p Λ =
    moduleDerivedInverseImageTensorSourceCounit p Λ ≫ modulePullbackHomotopyTensorHom p Λ

/-- The normalization determines the comparison uniquely.  This proposition is never used
to select a comparison: callers supply its actual natural transformation. -/
theorem moduleDerivedInverseImageTensorComparison_unique
    (α β : moduleDerivedInverseImageTensorComparison p Λ)
    (hα : moduleDerivedInverseImageTensorIsNormalized p Λ α)
    (hβ : moduleDerivedInverseImageTensorIsNormalized p Λ β) : α = β := sorry

/-- A component of a supplied functorial inverse-image tensor comparison. -/
def moduleDerivedInverseImageTensorHom
    (comparison : moduleDerivedInverseImageTensorComparison p Λ)
    (K L : DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleModuleDerivedInverseImage p Λ).obj (DerivedTensor.Bifunctor.obj K L) ⟶
      DerivedTensor.Bifunctor.obj
        ((etaleModuleDerivedInverseImage p Λ).obj K) ((etaleModuleDerivedInverseImage p Λ).obj L) :=
  comparison.app (K, L)

/-- Naturality in both derived inputs is part of the functor-level comparison. -/
theorem moduleDerivedInverseImageTensorHom_naturality
    (comparison : moduleDerivedInverseImageTensorComparison p Λ)
    {K K' L L' : DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))}
    (f : K ⟶ K') (g : L ⟶ L') :
    (etaleModuleDerivedInverseImage p Λ).map (DerivedTensor.Bifunctor.functor.map (f, g)) ≫
        moduleDerivedInverseImageTensorHom p Λ comparison K' L' =
      moduleDerivedInverseImageTensorHom p Λ comparison K L ≫
        DerivedTensor.Bifunctor.functor.map
          ((etaleModuleDerivedInverseImage p Λ).map f,
            (etaleModuleDerivedInverseImage p Λ).map g) :=
  comparison.naturality (X := (K, L)) (Y := (K', L')) (f, g)

/-- A normalized comparison is invertible.  No inverse is selected from this proposition. -/
theorem moduleDerivedInverseImageTensorHom_isIso
    (comparison : moduleDerivedInverseImageTensorComparison p Λ)
    (hcomparison : moduleDerivedInverseImageTensorIsNormalized p Λ comparison)
    (K L : DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))) :
    IsIso (moduleDerivedInverseImageTensorHom p Λ comparison K L) := sorry

end GeneralCoefficients

end AlgebraicGeometry.Scheme.Etale
