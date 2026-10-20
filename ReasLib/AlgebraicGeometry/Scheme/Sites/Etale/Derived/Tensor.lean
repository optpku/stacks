module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Universe
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ZMod
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor
public import Mathlib.CategoryTheory.Localization.Prod

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
  ((tensorIso (asIso (adj.counit.app (R.obj F))).symm
      (asIso (adj.counit.app (R.obj G))).symm) ≪≫
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

end AlgebraicGeometry.Scheme.Etale
