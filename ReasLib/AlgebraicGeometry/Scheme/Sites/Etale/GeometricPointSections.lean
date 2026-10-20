module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseImageStalk
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.NatIso

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale

/-- Global sections on the small étale site are evaluation at the identity étale object. -/
def etaleSectionsFunctor (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology (Type u) ⥤ Type u :=
  (sheafSections X.smallEtaleTopology (Type u)).obj
    (op (MorphismProperty.Over.mk _ (𝟙 X) inferInstance : X.Etale))

/-- Global sections send a sheaf morphism to its component at the identity étale object. -/
theorem etaleSectionsFunctor_map (X : Scheme.{u})
    {F G : Sheaf X.smallEtaleTopology (Type u)} (morphism : F ⟶ G) :
    (etaleSectionsFunctor X).map morphism =
      morphism.hom.app (op (MorphismProperty.Over.mk _ (𝟙 X) inferInstance : X.Etale)) := rfl

/-- The identity morphism is terminal in the small étale site. -/
def etaleIdentity_isTerminal (X : Scheme.{u}) :
    IsTerminal (MorphismProperty.Over.mk _ (𝟙 X) inferInstance : X.Etale) :=
  IsTerminal.ofUniqueHom
    (fun object ↦ MorphismProperty.Over.homMk object.hom (Category.comp_id _))
    (fun object morphism ↦ by
      apply MorphismProperty.Over.Hom.ext
      exact (Category.comp_id morphism.left).symm.trans
        (MorphismProperty.Over.w morphism))

/-- The constant sheaf functor is left adjoint to global sections on the small étale site. -/
def etaleConstantSheafAdj (X : Scheme.{u})
    [HasWeakSheafify X.smallEtaleTopology (Type u)] :
    constantSheaf X.smallEtaleTopology (Type u) ⊣ etaleSectionsFunctor X :=
  constantSheafAdj X.smallEtaleTopology (Type u) (etaleIdentity_isTerminal X)

/-- Over an algebraically closed field, the constant-sheaf adjunction unit is an isomorphism. -/
instance etaleConstantSheaf_unit_isIso (K : Type u) [Field K] [IsAlgClosed K]
    [HasWeakSheafify (Spec (.of K)).smallEtaleTopology (Type u)] (set : Type u) :
    IsIso ((etaleConstantSheafAdj (Spec (.of K))).unit.app set) := sorry

/-- Over an algebraically closed field, the constant-sheaf adjunction counit is an isomorphism. -/
instance etaleConstantSheaf_counit_isIso (K : Type u) [Field K] [IsAlgClosed K]
    [HasWeakSheafify (Spec (.of K)).smallEtaleTopology (Type u)]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)) :
    IsIso ((etaleConstantSheafAdj (Spec (.of K))).counit.app F) := sorry

/-- Étale sheaves on the spectrum of an algebraically closed field are equivalent to sets
by global sections, with inverse given by constant sheaves. -/
def etaleSheavesEquivType (K : Type u) [Field K] [IsAlgClosed K]
    [HasWeakSheafify (Spec (.of K)).smallEtaleTopology (Type u)] :
    Sheaf (Spec (.of K)).smallEtaleTopology (Type u) ≌ Type u :=
  (etaleConstantSheafAdj (Spec (.of K))).toEquivalence.symm

/-- The sections equivalence evaluates a sheaf at the identity étale object. -/
theorem etaleSheavesEquivType_functor_obj (K : Type u) [Field K] [IsAlgClosed K]
    [HasWeakSheafify (Spec (.of K)).smallEtaleTopology (Type u)]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)) :
    (etaleSheavesEquivType K).functor.obj F =
      F.obj.obj (op (MorphismProperty.Over.mk _ (𝟙 (Spec (.of K))) inferInstance :
        (Spec (.of K)).Etale)) := rfl

variable {S : Scheme.{u}}

/-- The stalk functor at a geometric point is the associated site-point sheaf fibre. -/
def stalkFunctor (s : GeometricPoint S) : Sheaf S.smallEtaleTopology (Type u) ⥤ Type u :=
  (GeometricPoint.toSmallEtalePoint s).sheafFiber

/-- The stalk functor evaluates to the site-point sheaf fibre. -/
theorem stalkFunctor_obj (s : GeometricPoint S) (F : Sheaf S.smallEtaleTopology (Type u)) :
    (stalkFunctor s).obj F = (GeometricPoint.toSmallEtalePoint s).sheafFiber.obj F := rfl

/-- The stalk functor agrees with the presheaf fibre of the underlying presheaf. -/
theorem stalkFunctor_eq_presheafFiber (s : GeometricPoint S)
    (F : Sheaf S.smallEtaleTopology (Type u)) :
    (stalkFunctor s).obj F = stalk s F.obj := rfl

/-- The source field of a geometric point gives an identity geometric point on its spectrum. -/
def idGeometricPoint (s : GeometricPoint S) : GeometricPoint (Spec (.of s.K)) :=
  @GeometricPoint.of (Spec (.of s.K)) s.K inferInstance s.isAlgClosed (𝟙 _)

/-- The identity lift defines the canonical germ from global sections to the identity stalk. -/
def identityStalkGerm (K : Type u) [Field K] [IsAlgClosed K] :
    etaleSectionsFunctor (Spec (.of K)) ⟶ stalkFunctor (GeometricPoint.of K (𝟙 _)) :=
  Functor.whiskerLeft (sheafToPresheaf (Spec (.of K)).smallEtaleTopology (Type u))
    ((GeometricPoint.toSmallEtalePoint (GeometricPoint.of K (𝟙 _))).toPresheafFiberNatTrans
      (MorphismProperty.Over.mk _ (𝟙 (Spec (.of K))) inferInstance)
      (Over.homMk (𝟙 (Spec (.of K))) (Category.comp_id _)))

/-- The identity germ is bijective on étale sheaves over an algebraically closed field. -/
theorem identityStalkGerm_bijective (K : Type u) [Field K] [IsAlgClosed K]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)) :
    Function.Bijective ((identityStalkGerm K).app F) := sorry

/-- Every component of the identity germ is an isomorphism. -/
instance identityStalkGerm_app_isIso (K : Type u) [Field K] [IsAlgClosed K]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)) :
    IsIso ((identityStalkGerm K).app F) :=
  (isIso_iff_bijective _).mpr (identityStalkGerm_bijective K F)

/-- The identity germ is a natural isomorphism. -/
instance identityStalkGerm_isIso (K : Type u) [Field K] [IsAlgClosed K] :
    IsIso (identityStalkGerm K) := NatIso.isIso_of_isIso_app _

/-- The identity stalk on an algebraically closed field spectrum is naturally global sections. -/
def identityStalkSectionsIso (K : Type u) [Field K] [IsAlgClosed K] :
    stalkFunctor (GeometricPoint.of K (𝟙 _)) ≅ etaleSectionsFunctor (Spec (.of K)) :=
  (asIso (identityStalkGerm K)).symm

/-- The image of the identity geometric point along its original morphism is the original point. -/
theorem imagePoint_idGeometricPoint (s : GeometricPoint S) :
    smallEtaleInverseImage_imagePoint s.hom (idGeometricPoint s) = s := by
  change (⟨FieldValuedPoint.of s.K (𝟙 _ ≫ s.hom), s.isAlgClosed⟩ : GeometricPoint S) = s
  rw [Category.id_comp]
  rfl

/-- Stalks at the image of the identity point are transported to stalks at the original point. -/
def stalkFunctor_imagePointIso (s : GeometricPoint S)
    (F : Sheaf S.smallEtaleTopology (Type u)) :
    (GeometricPoint.toSmallEtalePoint
        (smallEtaleInverseImage_imagePoint s.hom (idGeometricPoint s))).sheafFiber.obj F ≅
      (stalkFunctor s).obj F :=
  eqToIso (congrArg (fun point ↦ (stalkFunctor point).obj F)
    (imagePoint_idGeometricPoint s))

variable (s : GeometricPoint S)
variable [HasWeakSheafify (Spec (.of s.K)).smallEtaleTopology (Type u)]
variable [∀ P : S.Etaleᵒᵖ ⥤ Type u, (smallEtalePullback s.hom).op.HasLeftKanExtension P]

/-- Inverse image along a geometric point followed by global sections on its source spectrum. -/
def pullbackThenSections : Sheaf S.smallEtaleTopology (Type u) ⥤ Type u :=
  (smallEtalePullback s.hom).sheafPullback (Type u)
      S.smallEtaleTopology (Spec (.of s.K)).smallEtaleTopology ⋙
    etaleSectionsFunctor (Spec (.of s.K))

/-- Inverse image followed by sections evaluates the inverse-image sheaf at the identity object. -/
theorem pullbackThenSections_obj (F : Sheaf S.smallEtaleTopology (Type u)) :
    (pullbackThenSections s).obj F =
      (((smallEtalePullback s.hom).sheafPullback (Type u)
        S.smallEtaleTopology (Spec (.of s.K)).smallEtaleTopology).obj F).obj.obj
          (op (MorphismProperty.Over.mk _ (𝟙 (Spec (.of s.K))) inferInstance :
            (Spec (.of s.K)).Etale)) := rfl

/-- Germs, the inverse-image stalk comparison, and point transport are natural in sheaves. -/
theorem pullbackSectionsToStalk_naturality
    {F G : Sheaf S.smallEtaleTopology (Type u)} (morphism : F ⟶ G) :
    (pullbackThenSections s).map morphism ≫
        ((@identityStalkGerm s.K inferInstance s.isAlgClosed).app
          (((smallEtalePullback s.hom).sheafPullback (Type u)
            S.smallEtaleTopology (Spec (.of s.K)).smallEtaleTopology).obj G) ≫
          (smallEtaleInverseImage_stalkIso s.hom (idGeometricPoint s) G).hom ≫
          (stalkFunctor_imagePointIso s G).hom) =
      ((@identityStalkGerm s.K inferInstance s.isAlgClosed).app
          (((smallEtalePullback s.hom).sheafPullback (Type u)
            S.smallEtaleTopology (Spec (.of s.K)).smallEtaleTopology).obj F) ≫
          (smallEtaleInverseImage_stalkIso s.hom (idGeometricPoint s) F).hom ≫
          (stalkFunctor_imagePointIso s F).hom) ≫ (stalkFunctor s).map morphism := sorry

/-- Sections of inverse image map canonically to the original geometric stalk. -/
def pullbackSectionsToStalk : pullbackThenSections s ⟶ stalkFunctor s where
  app F :=
    (@identityStalkGerm s.K inferInstance s.isAlgClosed).app
        (((smallEtalePullback s.hom).sheafPullback (Type u)
          S.smallEtaleTopology (Spec (.of s.K)).smallEtaleTopology).obj F) ≫
      (smallEtaleInverseImage_stalkIso s.hom (idGeometricPoint s) F).hom ≫
      (stalkFunctor_imagePointIso s F).hom
  naturality _ _ morphism := pullbackSectionsToStalk_naturality s morphism

/-- The canonical comparison from inverse-image sections to a geometric stalk is an isomorphism. -/
instance pullbackSectionsToStalk_app_isIso (F : Sheaf S.smallEtaleTopology (Type u)) :
    IsIso ((pullbackSectionsToStalk s).app F) := sorry

/-- The sections-to-stalk comparison is a natural isomorphism. -/
instance pullbackSectionsToStalk_isIso :
    IsIso (pullbackSectionsToStalk s) := NatIso.isIso_of_isIso_app _

/-- The geometric stalk functor is naturally inverse image followed by global sections. -/
def stalkFunctorIsoPullback : stalkFunctor s ≅ pullbackThenSections s :=
  (asIso (pullbackSectionsToStalk s)).symm

/-- Each stalk-to-sections component is the inverse of the canonical sections-to-stalk map. -/
theorem stalkFunctorIsoPullback_app (F : Sheaf S.smallEtaleTopology (Type u)) :
    (stalkFunctorIsoPullback s).app F = (asIso ((pullbackSectionsToStalk s).app F)).symm := sorry

end AlgebraicGeometry.Scheme.Etale
