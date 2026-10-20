module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.Algebra.Homology.Bifunctor
public import ReasLib.CategoryTheory.Abelian.StructureTransport
public import ReasLib.CategoryTheory.DerivedCategory.Functor.KInjectiveModel
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Pullback

/-! # Derived global sections of small-étale module sheaves -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open Opposite ComplexShape
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

/-- Inverse image of module sheaves along a morphism of schemes is sheaf pullback
along `smallEtalePullback`. -/
theorem etaleModuleSheafPullback_eq (Λ : Type u) [Ring Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ) =
      (smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
        Y.smallEtaleTopology X.smallEtaleTopology :=
  rfl

/-- Inverse-image identification along equal morphisms, by substitution of the
morphism equality. -/
def etaleModuleSheafPullback_congr (Λ : Type u) [Ring Λ] {A B : Scheme.{u}}
    {p q : A ⟶ B} (h : p = q)
    [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback p).op.HasLeftKanExtension P]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback q).op.HasLeftKanExtension P] :
    Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ) ≅ Sheaf.smallEtaleInverseImage q (ModuleCat.{u} Λ) :=
  h ▸ Iso.refl _

/-- Pullback of module sheaves along a composite is the composite pullback. -/
def etaleModuleSheafPullback_comp (Λ : Type u) [Ring Λ] {A B C : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B)
    [HasWeakSheafify B.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasWeakSheafify C.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : A.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback p).op.HasLeftKanExtension P]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback q).op.HasLeftKanExtension P]
    [∀ P : A.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (q ≫ p)).op.HasLeftKanExtension P] :
    Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ) ⋙ Sheaf.smallEtaleInverseImage q (ModuleCat.{u} Λ) ≅
      Sheaf.smallEtaleInverseImage (q ≫ p) (ModuleCat.{u} Λ) :=
  let siteIso :
      smallEtalePullback p ⋙ smallEtalePullback q ≅ smallEtalePullback (q ≫ p) :=
    (MorphismProperty.Over.pullbackComp q p).symm
  Adjunction.leftAdjointCompIso
    ((smallEtalePullback p).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
      A.smallEtaleTopology B.smallEtaleTopology)
    ((smallEtalePullback q).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
      B.smallEtaleTopology C.smallEtaleTopology)
    ((smallEtalePullback (q ≫ p)).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
      A.smallEtaleTopology C.smallEtaleTopology)
    (sheafPushforwardContinuousComp' siteIso (ModuleCat.{u} Λ)
      A.smallEtaleTopology B.smallEtaleTopology C.smallEtaleTopology)

/-- Global sections of a sheaf of left `Λ`-modules at the identity étale object. -/
abbrev etaleModuleGamma (Λ : Type u) [Ring Λ] (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) ⥤ ModuleCat.{u} Λ :=
  (sheafSections X.smallEtaleTopology (ModuleCat.{u} Λ)).obj (op (Scheme.Etale.globalEtale X))

/-- Unfolding of module-valued global sections at the identity étale object. -/
theorem etaleModuleGamma_eq (Λ : Type u) [Ring Λ] (X : Scheme.{u}) :
    etaleModuleGamma Λ X =
      (sheafSections X.smallEtaleTopology (ModuleCat.{u} Λ)).obj (op (Scheme.Etale.globalEtale X)) :=
  rfl

/-- Inverse image of sheaves of left `Λ`-modules is additive. -/
instance instAdditive_etaleModuleSheafPullback (Λ : Type u) [Ring Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    @Functor.Additive
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) _ _
      Abelian.toPreadditive Abelian.toPreadditive
      (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)) :=
  sorry

/-- Inverse image of sheaves of left `Λ`-modules preserves finite limits. -/
instance instPreservesFiniteLimits_etaleModuleSheafPullback (Λ : Type u) [Ring Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    PreservesFiniteLimits (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)) :=
  sorry

/-- Inverse image of sheaves of left `Λ`-modules preserves finite colimits. -/
instance instPreservesFiniteColimits_etaleModuleSheafPullback (Λ : Type u) [Ring Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    PreservesFiniteColimits (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)) :=
  sorry

/-- The category of small-étale sheaves of modules over a ring is Grothendieck
abelian for any abelian structure on its underlying category. -/
instance instIsGrothendieckAbelian_etaleModuleSheaf (Λ : Type u) [Ring Λ]
    (X : Scheme.{u}) [a : Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))] :
    IsGrothendieckAbelian.{u} (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) := by
  exact Eq.mp
    (congrArg (fun b : Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) =>
      @IsGrothendieckAbelian.{u} (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) _ b)
      (Abelian.structure_eq _ a))
    (AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology
      X (ModuleCat.{u} Λ))

/-- Monoidal additivity for the native structure on small-étale module sheaves
holds for the preadditive structure of any abelian structure on the same category. -/
instance instMonoidalPreadditive_etaleModuleSheaf_abelian (Λ : Type u) [Ring Λ]
    (Y : Scheme.{u}) [a : Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
    [m : MonoidalCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
    [native : @MonoidalPreadditive
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) _
      (@Preadditive.fullSubcategory (Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ) _
        (@functorCategoryPreadditive Y.Etaleᵒᵖ (ModuleCat.{u} Λ) _ _
          ModuleCat.instPreadditive)
        (Presheaf.IsSheaf Y.smallEtaleTopology)) m] :
    @MonoidalPreadditive (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) _
      a.toPreadditive m := by
  let nativePreadditive : Preadditive (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    @Preadditive.fullSubcategory (Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ) _
      (@functorCategoryPreadditive Y.Etaleᵒᵖ (ModuleCat.{u} Λ) _ _
        ModuleCat.instPreadditive)
      (Presheaf.IsSheaf Y.smallEtaleTopology)
  have h : nativePreadditive = a.toPreadditive :=
    @Subsingleton.elim (Preadditive (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
      (@subsingleton_preadditive_of_hasBinaryBiproducts _ _
        (@Preadditive.preadditiveHasZeroMorphisms _ _ a.toPreadditive)
        (@Abelian.hasBinaryBiproducts _ _ a)) _ _
  exact Eq.mp (congrArg (fun b =>
    @MonoidalPreadditive (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) _ b m) h) native

/-- Integer cochain complexes of small-étale module sheaves admit tensor
totalization for the preadditive structure of any abelian structure. -/
instance instHasMapBifunctor_etaleModuleSheaf_abelian (Λ : Type u) [Ring Λ]
    (Y : Scheme.{u}) [a : Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
    [m : MonoidalCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
    [@MonoidalPreadditive (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) _
      a.toPreadditive m] :
    ∀ (K L : @CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) _
      (@Preadditive.preadditiveHasZeroMorphisms _ _ a.toPreadditive) ℤ _ _),
      @HomologicalComplex.HasMapBifunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) _ _ _
        ℤ ℤ ℤ (up ℤ) (up ℤ)
        (@Preadditive.preadditiveHasZeroMorphisms _ _ a.toPreadditive)
        (@Preadditive.preadditiveHasZeroMorphisms _ _ a.toPreadditive)
        a.toPreadditive K L
        (MonoidalCategory.curriedTensor (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
        (by
          exact @Functor.preservesZeroMorphisms_of_additive _ _ _ _ a.toPreadditive
            (@functorCategoryPreadditive _ _ _ _ a.toPreadditive) _ (by infer_instance))
        (by
          intro F
          exact @Functor.preservesZeroMorphisms_of_additive _ _ _ _ a.toPreadditive
            a.toPreadditive _ (by infer_instance)) (up ℤ) _ := by
  intro K L
  unfold HomologicalComplex.HasMapBifunctor HomologicalComplex₂.HasTotal GradedObject.HasMap
  intro j
  let colimits : HasColimitsOfSize.{u, u}
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    @IsGrothendieckAbelian.hasColimits.{u} _ _ a
      (instIsGrothendieckAbelian_etaleModuleSheaf Λ Y)
  let smallColimits : HasColimitsOfSize.{0, 0}
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    @hasColimitsOfSizeShrink.{0, 0, u, u} _ _ colimits
  exact @HasColimitsOfShape.has_colimit _ _ _ _
    (@HasColimitsOfSize.has_colimits_of_shape _ _ smallColimits _ _) _

/-- Global sections of sheaves of left `Λ`-modules are additive. -/
instance instAdditive_etaleModuleGamma (Λ : Type u) [Ring Λ] (X : Scheme.{u})
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))] :
    (etaleModuleGamma Λ X).Additive :=
  sorry

/-- Global sections of sheaves of left `Λ`-modules are additive with respect to
the `Abelian.toPreadditive` instances on source and target. -/
instance instAdditive_etaleModuleGamma_abelian (Λ : Type u) [Ring Λ] (X : Scheme.{u})
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [Abelian (ModuleCat.{u} Λ)] :
    @Functor.Additive
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
      (ModuleCat.{u} Λ) _ _
      Abelian.toPreadditive Abelian.toPreadditive
      (etaleModuleGamma Λ X) :=
  sorry

/-- The cochain functor of global sections of sheaves of left `Λ`-modules has
a total right derived functor for any choice of zero morphisms. With the zeros
of a preadditive structure, this is `RightDerived.Cochain.toDerived`. -/
instance instHasRightDerivedFunctor_etaleModuleGamma (Λ : Type u) [Ring Λ]
    (X : Scheme.{u})
    [a : Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (ModuleCat.{u} Λ)]
    [z : HasZeroMorphisms (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [(etaleModuleGamma Λ X).PreservesZeroMorphisms] :
    HasRightDerivedFunctor
      ((etaleModuleGamma Λ X).mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ)) := by
  have hz : z = @Preadditive.preadditiveHasZeroMorphisms
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) _ a.toPreadditive :=
    Subsingleton.elim _ _
  subst z
  exact KInjectiveModel.hasRightDerived (etaleModuleGamma Λ X)

/-- Pullback of underived global sections along inverse image of module sheaves. -/
def etaleModuleGammaPullback (Λ : Type u) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    etaleModuleGamma Λ Y ⟶
      Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ) ⋙ etaleModuleGamma Λ X where
  app F :=
    ((sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)).map
        (((smallEtalePullback f).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
            Y.smallEtaleTopology X.smallEtaleTopology).unit.app F)).app
      (op (Scheme.Etale.globalEtale Y)) ≫
      ((Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj F).obj.map
        (op (Scheme.Etale.globalEtalePullbackIso f).inv)
  naturality := fun _ _ _ ↦ sorry

/-- Component of the underived global-sections pullback at a sheaf, as the
adjunction unit followed by the identification of terminal étale objects. -/
theorem etaleModuleGammaPullback_app (Λ : Type u) [Ring Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (etaleModuleGammaPullback Λ f).app F =
      ((sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)).map
          (((smallEtalePullback f).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
              Y.smallEtaleTopology X.smallEtaleTopology).unit.app F)).app
        (op (Scheme.Etale.globalEtale Y)) ≫
        ((Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj F).obj.map
          (op (Scheme.Etale.globalEtalePullbackIso f).inv) :=
  rfl

/-- Derived étale global sections `RΓ(X, -)` of sheaves of left `Λ`-modules. -/
abbrev etaleModuleDerivedGamma (Λ : Type u) [Ring Λ] (X : Scheme.{u})
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (ModuleCat.{u} Λ)] :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
      DerivedCategory (ModuleCat.{u} Λ) :=
  RightDerived.Cochain.functor (etaleModuleGamma Λ X)

/-- `RΓ(X, -)` is the cochain-level total right derived functor of étale module
sections at `Scheme.Etale.globalEtale X`. -/
theorem etaleModuleDerivedGamma_spec (Λ : Type u) [Ring Λ] (X : Scheme.{u})
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (ModuleCat.{u} Λ)] :
    etaleModuleDerivedGamma Λ X =
      RightDerived.Cochain.functor (etaleModuleGamma Λ X) :=
  rfl

end AlgebraicGeometry.Scheme.Hom
