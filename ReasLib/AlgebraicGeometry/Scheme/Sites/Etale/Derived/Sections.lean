module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Specialization.Derived
public import ReasLib.CategoryTheory.Sites.Derived.SectionsComparison
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

/- Private implementation visibility justification: public comparison maps use private
cochain and germ constructions without exporting an implementation interface. -/
set_option backward.privateInPublic true

universe u

namespace AlgebraicGeometry.Scheme.Etale.Derived

variable {X S : Scheme.{u}}

/-- Abelian-group presheaves on the small étale site have canonical left-exact sheafification. -/
private abbrev sectionsSheafification (T : Scheme.{u}) :
    HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (@instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover
          T.Etale inferInstance T.smallEtaleTopology AddCommGrpCat.{u + 1} inferInstance
          (fun P U cover ↦ inferInstance) (fun U ↦ inferInstance)
          _ _ inferInstance inferInstance
          (fun U ↦ @PreservesFilteredColimitsOfSize.preserves_filtered_colimits _ _ _ _
            (CategoryTheory.forget AddCommGrpCat.{u + 1})
            AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
            (T.smallEtaleTopology.Cover U)ᵒᵖ inferInstance
            (@isFiltered_op_of_isCofiltered (T.smallEtaleTopology.Cover U) inferInstance
              (isCofiltered_of_semilatticeInf_nonempty (T.smallEtaleTopology.Cover U)))) inferInstance
          (fun {U} cover ↦ inferInstance) inferInstance inferInstance (fun U ↦ inferInstance))

/-- Abelian étale sheaves form an abelian category via left-exact sheafification. -/
private abbrev sectionsAbelian (T : Scheme.{u}) :
    CategoryTheory.Abelian (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  @sheafIsAbelian _ _ _ _ inferInstance _ (sectionsSheafification T)

/-- Global étale sections with the canonical sheafification evidence fixed. -/
private abbrev globalSectionsFunctor (T : Scheme.{u}) :=
  @siteAbelianSectionsFunctor.{u + 1, u, u + 1} T.Etale inferInstance
    T.smallEtaleTopology (globalEtale T) (sectionsSheafification T)

/-- Derived global étale sections with the canonical sheafification evidence fixed. -/
private abbrev globalSectionsDerived (T : Scheme.{u}) :=
  @siteAbelianSectionsDerived.{u + 1, u, u + 1} T.Etale inferInstance
    T.smallEtaleTopology (globalEtale T) (sectionsSheafification T) inferInstance


/-- Global sections of a direct image identify with global sections on its domain. -/
private def directImageSectionsUnderivedIso (f : X ⟶ S) :
    Abelian.directImage f ⋙
        globalSectionsFunctor S ≅
      globalSectionsFunctor X :=
  @SiteAbelianSectionsDerived.sectionsIso _ _ _ _ _ _ (smallEtalePullback f)
      inferInstance (sectionsSheafification S) (sectionsSheafification X) (globalEtale S) ≪≫
    (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
      (globalEtalePullbackIso f).symm.op

/-- The cochain sections functor identifies with direct image followed by cochain sections. -/
private def directImageSectionsCochainIso (f : X ⟶ S)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}] :
    Functor.RightDerived.Cochain.toDerived
        (globalSectionsFunctor X) ≅
      (Abelian.directImage f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        Functor.RightDerived.Cochain.toDerived
          (globalSectionsFunctor S) :=
  Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (directImageSectionsUnderivedIso f).symm
        (ComplexShape.up ℤ)) DerivedCategory.Q ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm
      DerivedCategory.Q ≪≫
    Functor.associator _ _ _

/-- The canonical comparison from derived global sections on the domain to derived global
sections of the derived direct image. -/
private def directImageSectionsComparisonConstruction (f : X ⟶ S)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}] :
    globalSectionsDerived X ⟶
      directImage f ⋙
        globalSectionsDerived S :=
  (globalSectionsDerived X).rightDerivedDesc
    (Functor.RightDerived.Cochain.unit
      (globalSectionsFunctor X))
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ)) _
    ((directImageSectionsCochainIso f).hom ≫
      Functor.RightDerived.Composition.iteratedUnit
        (Functor.RightDerived.KInjective.unit (Abelian.directImage f))
        (Functor.RightDerived.Cochain.unit
          (globalSectionsFunctor S)))

/-- The canonical comparison from derived global sections on the domain to derived global
sections of the derived direct image. -/
def directImageSectionsComparison (f : X ⟶ S) :
    globalSectionsDerived X ⟶ directImage f ⋙ globalSectionsDerived S :=
  @directImageSectionsComparisonConstruction X S f
    (sectionsSheafification X) (sectionsSheafification S)

/-- Derived global sections commute with the derived direct image. -/
instance directImageSectionsComparison_isIso (f : X ⟶ S) :
    IsIso (directImageSectionsComparison f) := sorry

/-- Derived global sections of the derived direct image identify with sections on the domain. -/
def directImageSectionsIso (f : X ⟶ S) :
    directImage f ⋙
        globalSectionsDerived S ≅
      globalSectionsDerived X :=
  (asIso (directImageSectionsComparison f)).symm

/-- Restriction of derived global sections along a scheme morphism. -/
def sectionsPullback (f : X ⟶ S) :
    globalSectionsDerived S ⟶
      inverseImage f ⋙
        globalSectionsDerived X :=
  (Functor.leftUnitor _).inv ≫
    whiskerRight (adjunction f).unit
      (globalSectionsDerived S) ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft (inverseImage f) (directImageSectionsIso f).hom

/-- The geometric point of its own spectrum with identity structure morphism. -/
private def identityGeometricPoint (s : GeometricPoint S) :
    GeometricPoint (Spec (.of s.K)) :=
  @GeometricPoint.of _ s.K inferInstance s.isAlgClosed (𝟙 _)

/-- Sections on the spectrum of a geometric field map to the identity-point stalk by germs. -/
private def identityPointGerm (s : GeometricPoint S) :
    globalSectionsFunctor (Spec (.of s.K)) ⟶
      (etaleStalkExact (identityGeometricPoint s)).obj :=
  (sheafSectionsNatIsoEvaluation
    (J := (Spec (.of s.K)).smallEtaleTopology) (A := AddCommGrpCat.{u + 1})
    (X := globalEtale (Spec (.of s.K)))).hom ≫
    whiskerLeft (sheafToPresheaf _ AddCommGrpCat.{u + 1})
      ((identityGeometricPoint s).toSmallEtalePoint.toPresheafFiberNatTrans
        (globalEtale (Spec (.of s.K))) (Over.homMk (𝟙 _) (Category.comp_id _)))

/-- The right-derived germ map from global sections on a geometric spectrum to its stalk. -/
private def identityPointDerivedGerm (s : GeometricPoint S)
    [HasSheafify (Spec (.of s.K)).smallEtaleTopology AddCommGrpCat.{u + 1}] :
    globalSectionsDerived (Spec (.of s.K)) ⟶
      (@ExactFunctor.mapDerivedCategory _ _ (sectionsAbelian (Spec (.of s.K))) _ _ _ _ _
        (etaleStalkExact (identityGeometricPoint s))) :=
  (globalSectionsDerived (Spec (.of s.K))).rightDerivedDesc
      (Functor.RightDerived.Cochain.unit
        (globalSectionsFunctor (Spec (.of s.K))))
      (HomologicalComplex.quasiIso
        (Sheaf (Spec (.of s.K)).smallEtaleTopology AddCommGrpCat.{u + 1})
        (ComplexShape.up ℤ)) _
      (whiskerRight (NatTrans.mapHomologicalComplex (identityPointGerm s)
          (ComplexShape.up ℤ)) DerivedCategory.Q ≫
        (etaleStalkExact (identityGeometricPoint s)).obj.mapDerivedCategoryFactors.inv)

/-- The identity-point stalk of the inverse image maps to the original geometric stalk. -/
private def geometricPointStalkComparison (s : GeometricPoint S) :
    (Abelian.inverseImageExact s.hom).comp (etaleStalkExact (identityGeometricPoint s)) ⟶
      etaleStalkExact s :=
  let geometric := identityGeometricPoint s
  let overIso : Over.mk (geometric.hom ≫ s.hom) ≅ Over.mk s.hom :=
    Over.isoMk (Iso.refl _)
      ((Category.id_comp s.hom).trans (Category.id_comp s.hom).symm)
  let fiberTransport := Functor.whiskerLeft (Etale.forget S) (coyoneda.map overIso.inv.op)
  ObjectProperty.homMk
    ((geometric.toSmallEtalePoint.sheafFiberComapIsoOfMorphismOfSites
      (J := S.smallEtaleTopology)
      (h_adj := (Abelian.adjunction s.hom).isRightAdjoint)
      (h_small := smallEtalePullback_fiber_initiallySmall s.hom s.K geometric.hom)
      (smallEtalePullback s.hom) AddCommGrpCat.{u + 1}).inv ≫
      GrothendieckTopology.Point.Hom.sheafFiber
        ⟨smallEtaleInverseImage_comapFiberHom s.hom geometric⟩ ≫
      GrothendieckTopology.Point.Hom.sheafFiber ⟨fiberTransport⟩)

/-- The canonical germ map identifies sections after pullback to a geometric point with its
derived geometric stalk. -/
def geometricPointSectionsToStalk (s : GeometricPoint S) :
    inverseImage s.hom ⋙
        globalSectionsDerived (Spec (.of s.K)) ⟶
      (@ExactFunctor.mapDerivedCategory _ _ (sectionsAbelian S) _ _ _ _ _ (etaleStalkExact s)) :=
  whiskerLeft (inverseImage s.hom) (@identityPointDerivedGerm S s (sectionsSheafification (Spec (.of s.K)))) ≫
    (@ExactFunctor.MapDerivedCategory.compFunctorIso _ _ (sectionsAbelian S) _
      _ _ (sectionsAbelian (Spec (.of s.K))) _ _ _ _ _
      (Abelian.inverseImageExact s.hom) (etaleStalkExact (identityGeometricPoint s))).inv ≫
    @ExactFunctor.MapDerivedCategory.map _ _ (sectionsAbelian S) _ _ _ _ _ _ _
      (geometricPointStalkComparison s)

/-- Sections after pullback to a geometric point identify with the geometric stalk. -/
theorem geometricPointSectionsToStalk_isIso (s : GeometricPoint S) :
    IsIso (geometricPointSectionsToStalk s) := sorry

/-- The geometric stalk identifies with derived sections after geometric-point pullback. -/
def geometricPointSectionsIso (s : GeometricPoint S) :
    (@ExactFunctor.mapDerivedCategory _ _ (sectionsAbelian S) _ _ _ _ _ (etaleStalkExact s)) ≅
      inverseImage s.hom ⋙
        globalSectionsDerived (Spec (.of s.K)) :=
  (@asIso _ _ _ _ (geometricPointSectionsToStalk s) (geometricPointSectionsToStalk_isIso s)).symm

end AlgebraicGeometry.Scheme.Etale.Derived

end
