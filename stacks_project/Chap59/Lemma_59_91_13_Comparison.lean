module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality.Iso
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow.Exact.Degree
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Homology
public import ReasLib.CategoryTheory.Sites.Derived.SectionsComparison
public import ReasLib.CategoryTheory.Sites.Point.MorphismOfSites
public import stacks_project.Chap59.Lemma_59_36_2_Stalk
public import stacks_project.Chap59.Lemma_59_91_12_BaseChange
public import stacks_project.Chap59.Remark_59_56_6_StalkFunctor
public import stacks_project.Chap59.Theorem_59_51_3_Cohomology

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf
open CategoryTheory.GrothendieckTopology.Point
open CategoryTheory.Functor.RightDerived.Composition.BoundedBelow
open Opposite

noncomputable section

universe w u

namespace AlgebraicGeometry.Scheme.Hom

/-- The scheme-theoretic geometric fibre `ȳ ×_Y X` of `f` at a geometric point `ȳ` of `Y`. -/
noncomputable abbrev geometricFiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ybar : GeometricPoint Y) : Scheme.{u} :=
  pullback ybar.hom f

/-- `geometricFiber` is the chosen fibre product `ȳ ×_Y X`. -/
theorem geometricFiber_def {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y) :
    geometricFiber f ybar = pullback ybar.hom f :=
  rfl

/-- The structure morphism `f' : ȳ ×_Y X ⟶ Spec κ(ȳ)` of the geometric fibre. -/
noncomputable abbrev geometricFiberToPoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ybar : GeometricPoint Y) :
    geometricFiber f ybar ⟶ Spec (.of ybar.K) :=
  pullback.fst ybar.hom f

/-- `geometricFiberToPoint` is the first projection of `ȳ ×_Y X`. -/
theorem geometricFiberToPoint_def {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ybar : GeometricPoint Y) :
    geometricFiberToPoint f ybar = pullback.fst ybar.hom f :=
  rfl

/-- The base-change morphism `g' : ȳ ×_Y X ⟶ X` of the geometric fibre. -/
noncomputable abbrev geometricFiberToX {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ybar : GeometricPoint Y) :
    geometricFiber f ybar ⟶ X :=
  pullback.snd ybar.hom f

/-- `geometricFiberToX` is the second projection of `ȳ ×_Y X`. -/
theorem geometricFiberToX_def {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ybar : GeometricPoint Y) :
    geometricFiberToX f ybar = pullback.snd ybar.hom f :=
  rfl

/-- The cartesian square presenting the geometric fibre, in the `59.91.12` orientation
`g'`, `f'` over `f`, `ȳ`. -/
theorem geometricFiber_isPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ybar : GeometricPoint Y) :
    IsPullback (geometricFiberToX f ybar) (geometricFiberToPoint f ybar) f ybar.hom :=
  (IsPullback.of_hasPullback ybar.hom f).flip

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]

/-- Inverse image of an abelian small-étale sheaf along the geometric-fibre inclusion. -/
noncomputable abbrev geometricFiberSheaf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ybar : GeometricPoint Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf (geometricFiber f ybar).smallEtaleTopology AddCommGrpCat.{u} :=
  abelianPullbackAlong (geometricFiberToX f ybar) F

variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- Derived inverse image of a bounded-below complex along the geometric-fibre inclusion. -/
noncomputable abbrev geometricFiberDerived {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ybar : GeometricPoint Y)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    DerivedCategory.Plus
      (Sheaf (geometricFiber f ybar).smallEtaleTopology AddCommGrpCat.{u}) :=
  (etaleDerivedInverseImage (geometricFiberToX f ybar)).obj E

/-- Over-isomorphism identifying `id ≫ ȳ` with `ȳ`. -/
noncomputable def geometricPoint_idCompOverIso {Y : Scheme.{u}} (ybar : GeometricPoint Y) :
    Over.mk (𝟙 (Spec (.of ybar.K)) ≫ ybar.hom) ≅ Over.mk ybar.hom :=
  Over.isoMk (Iso.refl _) (Category.id_comp ybar.hom)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y)
variable [HasWeakSheafify (Spec (.of ybar.K)).smallEtaleTopology (Type u)]
variable [HasWeakSheafify Y.smallEtaleTopology (Type u)]
variable [∀ P : Y.Etaleᵒᵖ ⥤ Type u,
  (smallEtalePullback ybar.hom).op.HasLeftKanExtension P]
variable [InitiallySmall
    ((smallEtalePullback ybar.hom ⋙
        (GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).fiber).Elements)]
variable [((smallEtalePullback ybar.hom).sheafPushforwardContinuous (Type u)
    Y.smallEtaleTopology (Spec (.of ybar.K)).smallEtaleTopology).IsRightAdjoint]
variable [HasColimitsOfSize.{u, u} AddCommGrpCat.{u}]
variable [HasProducts.{u} AddCommGrpCat.{u}]

/-- Fibre map from the `id ≫ ȳ` site-point to `ȳ`. -/
noncomputable def geometricPoint_idCompFiberHom :
    (GeometricPoint.toSmallEtalePoint
        (smallEtaleInverseImage_imagePoint ybar.hom (idGeometricPoint ybar))).fiber ⟶
      (GeometricPoint.toSmallEtalePoint ybar).fiber where
  app V :=
    TypeCat.ofHom fun α => (geometricPoint_idCompOverIso ybar).inv ≫ α
  naturality := fun _ _ _ => sorry

/-- Fibre map from `ȳ` to the `id ≫ ȳ` site-point. -/
noncomputable def geometricPoint_idCompFiberInv :
    (GeometricPoint.toSmallEtalePoint ybar).fiber ⟶
      (GeometricPoint.toSmallEtalePoint
          (smallEtaleInverseImage_imagePoint ybar.hom (idGeometricPoint ybar))).fiber where
  app V :=
    TypeCat.ofHom fun α => (geometricPoint_idCompOverIso ybar).hom ≫ α
  naturality := fun _ _ _ => sorry

/-- Induced map on abelian sheaf fibres along a morphism of small-étale site-points of `Y`. -/
noncomputable abbrev abelianSheafFiberHom {Φ₁ Φ₂ : Y.smallEtaleTopology.Point}
    (t : Φ₁ ⟶ Φ₂) :
    (Φ₂.sheafFiber : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}) ⟶
      (Φ₁.sheafFiber : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}) :=
  Functor.whiskerLeft (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (Hom.presheafFiber t)

/-- Abelian sheaf-fibre comparison of the comap site-point of `id_{Spec κ(ȳ)}` along `ȳ`
with the stalk at `id ≫ ȳ`. -/
noncomputable def abelianComapStalkIso
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    ((GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).comapOfMorphismOfSites
          (smallEtalePullback ybar.hom)).sheafFiber.obj G ≅
      (GeometricPoint.toSmallEtalePoint
          (smallEtaleInverseImage_imagePoint ybar.hom
            (idGeometricPoint ybar))).sheafFiber.obj G where
  hom :=
    (abelianSheafFiberHom
        ⟨smallEtaleInverseImage_comapFiberHom ybar.hom (idGeometricPoint ybar)⟩).app G
  inv :=
    (abelianSheafFiberHom
        ⟨smallEtaleInverseImage_comapFiberInv ybar.hom (idGeometricPoint ybar)⟩).app G
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Abelian sheaf-fibre comparison of the stalk at `id ≫ ȳ` with the stalk at `ȳ`. -/
noncomputable def abelianImagePointStalkIso
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (GeometricPoint.toSmallEtalePoint
        (smallEtaleInverseImage_imagePoint ybar.hom
          (idGeometricPoint ybar))).sheafFiber.obj G ≅
      (GeometricPoint.toSmallEtalePoint ybar).sheafFiber.obj G where
  hom :=
    (abelianSheafFiberHom ⟨geometricPoint_idCompFiberHom ybar⟩).app G
  inv :=
    (abelianSheafFiberHom ⟨geometricPoint_idCompFiberInv ybar⟩).app G
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Pulling back by `ȳ → Y` produces the stalk: the abelian sheaf fibre of `G` at `ȳ`
identifies with the unique-point fibre of `ȳ⁻¹ G`. -/
noncomputable def abelianStalkPullbackIso
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (GeometricPoint.toSmallEtalePoint ybar).sheafFiber.obj G ≅
      (GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.obj
        ((etaleAbelianSheafPullback ybar.hom).obj G) :=
  (abelianImagePointStalkIso ybar G).symm ≪≫
    (abelianComapStalkIso ybar G).symm ≪≫
      ((GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiberComapIsoOfMorphismOfSites
          (smallEtalePullback ybar.hom) AddCommGrpCat.{u}).app G

/-- Forward map of `abelianStalkPullbackIso`. -/
theorem abelianStalkPullbackIso_hom
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (abelianStalkPullbackIso ybar G).hom =
      (abelianImagePointStalkIso ybar G).inv ≫
        (abelianComapStalkIso ybar G).inv ≫
          ((GeometricPoint.toSmallEtalePoint
                (idGeometricPoint ybar)).sheafFiberComapIsoOfMorphismOfSites
              (smallEtalePullback ybar.hom) AddCommGrpCat.{u}).hom.app G :=
  sorry

/-- Unique-point sheaf fibre on `Spec κ(ȳ)` compared with global sections at `globalEtale`. -/
noncomputable def uniquePointSheafFiberIsoSections :
    ((GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
        Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
          AddCommGrpCat.{u}) ≅
      siteAbelianSectionsFunctor (Spec (.of ybar.K)).smallEtaleTopology
        (globalEtale (Spec (.of ybar.K))) :=
  NatIso.ofComponents
    (fun G ↦
      { hom :=
          (GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).presheafFiberDesc
            (fun U x ↦
              G.obj.map (op (MorphismProperty.Over.homMk x.left sorry :
                globalEtale (Spec (.of ybar.K)) ⟶ U)))
            sorry
        inv :=
          (GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).toPresheafFiber
            (globalEtale (Spec (.of ybar.K)))
            (𝟙 (Over.mk (𝟙 (Spec (.of ybar.K))))) G.obj
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (fun _ => sorry)

/-- Global sections on `Spec κ(ȳ)` of a pushforward along the fibre structure morphism
identify with global sections on the geometric fibre. -/
noncomputable def geometricFiberPushforwardSectionsIso :
    abelianPushforwardAlong (geometricFiberToPoint f ybar) ⋙
        siteAbelianSectionsFunctor (Spec (.of ybar.K)).smallEtaleTopology
          (globalEtale (Spec (.of ybar.K))) ≅
      siteAbelianSectionsFunctor (geometricFiber f ybar).smallEtaleTopology
        (globalEtale (geometricFiber f ybar)) :=
  SiteAbelianSectionsDerived.sectionsIso
      (smallEtalePullback (geometricFiberToPoint f ybar))
      (globalEtale (Spec (.of ybar.K))) ≪≫
    (sheafSections (geometricFiber f ybar).smallEtaleTopology AddCommGrpCat.{u}).mapIso
      (Iso.op (globalEtalePullbackIso (geometricFiberToPoint f ybar)).symm)

variable
    [(etalePullbackExact ybar.hom).obj.PreservesHomology]
    [(etalePullbackExact (geometricFiberToX f ybar)).obj.PreservesInjectiveObjects]
    [(etalePullbackExact (geometricFiberToX f ybar)).obj.PreservesHomology]
    [((GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
        Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
          AddCommGrpCat.{u}).Additive]
    [((GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
        Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
          AddCommGrpCat.{u}).PreservesHomology]
    [PreservesFiniteLimits
      ((GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
        Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
          AddCommGrpCat.{u})]
    [PreservesFiniteColimits
      ((GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
        Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
          AddCommGrpCat.{u})]
    [(siteAbelianSectionsFunctor (Spec (.of ybar.K)).smallEtaleTopology
        (globalEtale (Spec (.of ybar.K)))).PreservesHomology]
    [HasExt.{u} (Sheaf (geometricFiber f ybar).smallEtaleTopology AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u})]
    [HasDerivedCategory.{w} AddCommGrpCat.{u}]

/-- Canonical comparison `(R^n f_* F)_ȳ ⟶ H^n_étale(X_ȳ, F_ȳ)` of abelian groups. -/
noncomputable def higherDirectImageStalkToGeometricFiberCohomology
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    (GeometricPoint.toSmallEtalePoint ybar).sheafFiber.obj
        (((abelianPushforwardAlong f).rightDerived n).obj F) ⟶
      ((siteAbelianSectionsFunctor (geometricFiber f ybar).smallEtaleTopology
          (globalEtale (geometricFiber f ybar))).rightDerived n).obj
        (geometricFiberSheaf f ybar F) :=
  (abelianStalkPullbackIso ybar
      (((abelianPushforwardAlong f).rightDerived n).obj F)).hom ≫
    (GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
      ((Functor.RightDerived.postcompExactIso (abelianPushforwardAlong f)
          (etalePullbackExact ybar.hom) n).inv.app F) ≫
    (GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
      (higherDirectImage_baseChangeHom f ybar.hom
        (geometricFiberToPoint f ybar) (geometricFiberToX f ybar)
        (geometricFiber_isPullback f ybar) F n) ≫
    (GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
      ((Functor.RightDerived.precompExactIso (etalePullbackExact (geometricFiberToX f ybar))
          (abelianPushforwardAlong (geometricFiberToPoint f ybar)) n).hom.app F) ≫
    (uniquePointSheafFiberIsoSections ybar).hom.app
      (((abelianPushforwardAlong (geometricFiberToPoint f ybar)).rightDerived n).obj
        (geometricFiberSheaf f ybar F)) ≫
    (Functor.RightDerived.postcompIso
        (abelianPushforwardAlong (geometricFiberToPoint f ybar))
        (siteAbelianSectionsFunctor (Spec (.of ybar.K)).smallEtaleTopology
          (globalEtale (Spec (.of ybar.K)))) n).inv.app
      (geometricFiberSheaf f ybar F) ≫
    (NatIso.rightDerived (geometricFiberPushforwardSectionsIso f ybar) n).hom.app
      (geometricFiberSheaf f ybar F)

/-- `higherDirectImageStalkToGeometricFiberCohomology` is the composite of abelian
stalk-pullback, the degree-`n` proper base-change comparison on `ȳ ×_Y X`, and the
unique-point identification of `R^n f'_*` with étale cohomology of the fibre. -/
theorem higherDirectImageStalkToGeometricFiberCohomology_eq
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    higherDirectImageStalkToGeometricFiberCohomology f ybar F n =
      (abelianStalkPullbackIso ybar
          (((abelianPushforwardAlong f).rightDerived n).obj F)).hom ≫
        (GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
          ((Functor.RightDerived.postcompExactIso (abelianPushforwardAlong f)
              (etalePullbackExact ybar.hom) n).inv.app F) ≫
        (GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
          (higherDirectImage_baseChangeHom f ybar.hom
            (geometricFiberToPoint f ybar) (geometricFiberToX f ybar)
            (geometricFiber_isPullback f ybar) F n) ≫
        (GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
          ((Functor.RightDerived.precompExactIso (etalePullbackExact (geometricFiberToX f ybar))
              (abelianPushforwardAlong (geometricFiberToPoint f ybar)) n).hom.app F) ≫
        (uniquePointSheafFiberIsoSections ybar).hom.app
          (((abelianPushforwardAlong (geometricFiberToPoint f ybar)).rightDerived n).obj
            (geometricFiberSheaf f ybar F)) ≫
        (Functor.RightDerived.postcompIso
            (abelianPushforwardAlong (geometricFiberToPoint f ybar))
            (siteAbelianSectionsFunctor (Spec (.of ybar.K)).smallEtaleTopology
              (globalEtale (Spec (.of ybar.K)))) n).inv.app
          (geometricFiberSheaf f ybar F) ≫
        (NatIso.rightDerived (geometricFiberPushforwardSectionsIso f ybar) n).hom.app
          (geometricFiberSheaf f ybar F) :=
  rfl

variable
    [(abelianPushforwardAlong f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong (geometricFiberToPoint f ybar)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (geometricFiber f ybar).smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact ybar.hom).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact (geometricFiberToX f ybar)).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong f ⋙ (etalePullbackExact ybar.hom).obj).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [((etalePullbackExact (geometricFiberToX f ybar)).obj ⋙
        abelianPushforwardAlong (geometricFiberToPoint f ybar)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong (geometricFiberToPoint f ybar) ⋙
        ((GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
          Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
            AddCommGrpCat.{u})).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (geometricFiber f ybar).smallEtaleTopology AddCommGrpCat.{u}))]
    [(siteAbelianSectionsFunctor (geometricFiber f ybar).smallEtaleTopology
        (globalEtale (geometricFiber f ybar))).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (geometricFiber f ybar).smallEtaleTopology AddCommGrpCat.{u}))]
    [EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [EnoughInjectives (Sheaf (geometricFiber f ybar).smallEtaleTopology AddCommGrpCat.{u})]
    [EnoughInjectives (Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u})]
    (h_src : IsIso (derivedSourceComparison f ybar.hom))

/-- Unique-point homology of `Rf'_* E'` identifies with derived étale cohomology of the
geometric fibre. -/
noncomputable def derivedUniquePointHomologyIsoFibreCohomology
    (E' : DerivedCategory.Plus
      (Sheaf (geometricFiber f ybar).smallEtaleTopology AddCommGrpCat.{u})) (n : ℤ) :
    (GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.obj
        ((DerivedCategory.Plus.homologyFunctor
            (Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u}) n).obj
          ((etaleDerivedPushforward (geometricFiberToPoint f ybar)).obj E')) ≅
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        (DerivedCategory.Plus.ι.obj
          ((Functor.RightDerived.Bounded.functor
              (siteAbelianSectionsFunctor (geometricFiber f ybar).smallEtaleTopology
                (globalEtale (geometricFiber f ybar)))).obj E')) :=
  (ExactFunctor.Derived.Plus.homologyIso
      (ExactFunctor.of
        ((GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
          Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
            AddCommGrpCat.{u}))
      ((etaleDerivedPushforward (geometricFiberToPoint f ybar)).obj E') n).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).mapIso
      ((ExactSecond.iso (abelianPushforwardAlong (geometricFiberToPoint f ybar))
          (ExactFunctor.of
            ((GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
              Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
                AddCommGrpCat.{u}))).app E') ≪≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).mapIso
      ((Functor.RightDerived.Bounded.mapIso
          (Functor.isoWhiskerLeft (abelianPushforwardAlong (geometricFiberToPoint f ybar))
              (uniquePointSheafFiberIsoSections ybar) ≪≫
            geometricFiberPushforwardSectionsIso f ybar)).app E')

/-- Canonical comparison `(R^n f_* E)_ȳ ⟶ H^n_étale(X_ȳ, E|_{X_ȳ})` of abelian groups. -/
noncomputable def derivedHigherDirectImageStalkToGeometricFiberCohomology
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (n : ℤ) :
    (GeometricPoint.toSmallEtalePoint ybar).sheafFiber.obj
        ((DerivedCategory.homologyFunctor
            (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) n).obj
          (DerivedCategory.Plus.ι.obj ((etaleDerivedPushforward f).obj E))) ⟶
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        (DerivedCategory.Plus.ι.obj
          ((Functor.RightDerived.Bounded.functor
              (siteAbelianSectionsFunctor (geometricFiber f ybar).smallEtaleTopology
                (globalEtale (geometricFiber f ybar)))).obj
            (geometricFiberDerived f ybar E))) :=
  (abelianStalkPullbackIso ybar
      ((DerivedCategory.homologyFunctor
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) n).obj
        (DerivedCategory.Plus.ι.obj ((etaleDerivedPushforward f).obj E)))).hom ≫
    (GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
      ((ExactFunctor.Derived.Plus.homologyIso (etalePullbackExact ybar.hom)
          ((etaleDerivedPushforward f).obj E) n).inv) ≫
    (GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
      ((DerivedCategory.Plus.homologyFunctor
          (Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u}) n).map
        (derivedBaseChangeHom f ybar.hom (geometricFiberToPoint f ybar)
          (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) h_src E)) ≫
    (derivedUniquePointHomologyIsoFibreCohomology f ybar
        (geometricFiberDerived f ybar E) n).hom

/-- `derivedHigherDirectImageStalkToGeometricFiberCohomology` is assembled from abelian
stalk-pullback, derived proper base change, and derived fibre sections. -/
theorem derivedHigherDirectImageStalkToGeometricFiberCohomology_eq
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (n : ℤ) :
    derivedHigherDirectImageStalkToGeometricFiberCohomology f ybar h_src E n =
      (abelianStalkPullbackIso ybar
          ((DerivedCategory.homologyFunctor
              (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) n).obj
            (DerivedCategory.Plus.ι.obj ((etaleDerivedPushforward f).obj E)))).hom ≫
        (GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
          ((ExactFunctor.Derived.Plus.homologyIso (etalePullbackExact ybar.hom)
              ((etaleDerivedPushforward f).obj E) n).inv) ≫
        (GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
          ((DerivedCategory.Plus.homologyFunctor
              (Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u}) n).map
            (derivedBaseChangeHom f ybar.hom (geometricFiberToPoint f ybar)
              (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) h_src E)) ≫
        (derivedUniquePointHomologyIsoFibreCohomology f ybar
            (geometricFiberDerived f ybar E) n).hom :=
  rfl

end AlgebraicGeometry.Scheme.Hom

end

end
