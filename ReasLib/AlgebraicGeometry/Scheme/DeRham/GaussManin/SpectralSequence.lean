/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.RelativeSpectralSequence
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.GaussManin.DifferentialGraded
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.DegreeZero
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageOneRow

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory
open AlgebraicGeometry.Scheme.Modules.Kunneth
open FilteredComplex.Cohomology.Convergence
open SheafOfModules.RingedSite RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/-- The relative de Rham cohomology sheaf `H^q(Rf_* Ω^•_{X/Y})` on `Y`. -/
noncomputable abbrev relativeDeRhamCohomology {X Y : Scheme.{u}}
    (f : X ⟶ Y) (q : ℤ)
    [hPush : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u, u, u, u} (coefficientSite f))] :
    RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y)) :=
  (@DerivedCategory.homologyFunctor
    (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
      (coefficientSite (𝟙 Y))) q).obj
      ((@modulePushforwardDerived.{u, u, u, u, u, u}
          _ _ (DerivedPushforward.pushforwardHom f) inferInstance inferInstance hPush).obj
        (DerivedPushforward.derivedComplex f))

/-- Relative de Rham cohomology after restriction of scalars along `b : Y ⟶ S`. -/
noncomputable abbrev restrictedRelativeDeRhamCohomology {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (b : Y ⟶ S) (q : ℤ)
    [hPush : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u, u, u, u} (coefficientSite f))] :
    RingedSite.ModuleCat.{u, u, u, u} (coefficientSite b) :=
  (modulePushforward (scalarRestrictionHom b)).obj
    (relativeDeRhamCohomology f q)

/-- The sheaf `Ω^p_{Y/S}`, regarded as a module on the identity coefficient site of `Y`. -/
noncomputable abbrev relativeFormModule {Y S : Scheme.{u}}
    (b : Y ⟶ S) (p : ℕ) :
    RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y)) :=
  (restrictionAlong
    (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap (𝟙 Y))).obj
      (RingedSpace.DeRham.form b.toLRSHom.toShHom p)

/-- The underived tensor product `Ω^p_{Y/S} ⊗_{𝒪_Y} H^q_{dR}(X/Y)`. -/
noncomputable abbrev gaussManinTensor {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (b : Y ⟶ S) (p : ℕ) (q : ℤ)
    [hPush : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u, u, u, u} (coefficientSite f))] :
    RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y)) :=
  MonoidalCategory.tensorObj (relativeFormModule b p) (relativeDeRhamCohomology f q)

/-- The tensor product `Ω^p_{Y/S} ⊗_{𝒪_Y} H^q_{dR}(X/Y)`, restricted to
`b⁻¹𝒪_S`. -/
noncomputable abbrev gaussManinTerm {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (b : Y ⟶ S) (p : ℕ) (q : ℤ)
    [hPush : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u, u, u, u} (coefficientSite f))] :
    RingedSite.ModuleCat.{u, u, u, u} (coefficientSite b) :=
  (modulePushforward (scalarRestrictionHom b)).obj
    (gaussManinTensor f b p q)

/-- The canonical degree-zero relative form determined by the unit section. -/
noncomputable def relativeFormZeroUnit {Y S : Scheme.{u}} (b : Y ⟶ S) :
    𝟙_ (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) ⟶
      relativeFormModule b 0 :=
  (tensorUnitToUnitModule.{u, u, u} :
      𝟙_ (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) ⟶ _) ≫
    (relativeFormModule b 0).unitHomEquiv.symm (gaussManinDeRhamOneSection b)

-- Local instance justification (defeq pin): the exact-tensor homology comparison must use the same ringed-site derived-category owner as `relativePageOneTerm`.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

section

variable {X Y S : Scheme.{u}} {f : X ⟶ Y} {b : Y ⟶ S}
variable [hPush : Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{u, u, u, u, u, u} (DerivedPushforward.pushforwardHom f))
  (ModuleQis.{u, u, u, u} (coefficientSite f))]

/-- Exact tensoring on the right by the flat relative de Rham cohomology sheaf in degree `q`. -/
noncomputable def gaussManinExactTensor
    (q : ℤ)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r)) :
    (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) ⥤ₑ
      (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) :=
  @MonoidalCategory.IsFlat.exactTensorRight _ _ _
    (relativeDeRhamCohomology f q) (hFlat q)

/-- The derived functor induced by exact tensoring with the flat degree-`q` cohomology sheaf. -/
noncomputable def gaussManinExactTensorDerived
    (q : ℤ)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r)) :
    @DerivedCategory _ _ _
        (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite (𝟙 Y))) ⥤
      @DerivedCategory _ _ _
        (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite (𝟙 Y))) :=
  @Functor.mapDerivedCategory _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite (𝟙 Y)))
    _ _ _ (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite (𝟙 Y)))
    (gaussManinExactTensor q hFlat).obj _ _ _

/-- The homology term obtained by exact tensoring with the flat degree-`q` relative de Rham
cohomology sheaf and then restricting scalars to `b⁻¹𝒪_S`. -/
noncomputable abbrev gaussManinExactTensorHomologyTerm
    (q : ℤ)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (p : ℕ) :
    RingedSite.ModuleCat.{u, u, u, u} (coefficientSite b) :=
  (modulePushforward (scalarRestrictionHom b)).obj
    ((@DerivedCategory.homologyFunctor _ _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite (𝟙 Y))) 0).obj
        ((gaussManinExactTensorDerived q hFlat).obj (formDerived b p)))

/-- The canonical exact-tensor/homology comparison, restricted from `𝒪_Y`-modules to
`b⁻¹𝒪_S`-modules. -/
noncomputable def gaussManinExactTensorHomologyIso
    (q : ℤ)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (p : ℕ) :
    gaussManinExactTensorHomologyTerm q hFlat p ≅ gaussManinTerm f b p q :=
  (modulePushforward (scalarRestrictionHom b)).mapIso
    ((@Functor.MapDerivedCategory.homologyIso _ _ _
        (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite (𝟙 Y)))
        _ _ _ (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite (𝟙 Y)))
        (gaussManinExactTensor q hFlat).obj _ _ _ (formDerived b p) 0) ≪≫
      (gaussManinExactTensor q hFlat).obj.mapIso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app
          (relativeFormModule b p)))

end

namespace RelativeSpectralSequence

/-- Explicit multiplicative comparison and action data on a relative de Rham spectral sequence. -/
structure CupWedge {X Y S : Scheme.{u}} (f : X ⟶ Y) (b : Y ⟶ S)
    [hPush : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u, u, u, u} (coefficientSite f))]
    [hRestr : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (scalarRestrictionHom b))
      (ModuleQis.{u, u, u, u} (coefficientSite (𝟙 Y)))]
    [hTensor : @DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
        (coefficientSite (𝟙 Y))) _ _ _ _ _ _ _]
    (E : CohomologicalSpectralSequence
      (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite b)) 0) where
  /-- The flat derived-tensor comparison before commuting exact tensor with homology. -/
  flatDerivedTensorComparison :
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r)) →
      ∀ (p : ℕ) (q : ℤ), relativePageOneTerm f b p q ⟶
        gaussManinExactTensorHomologyTerm q hFlat p
  /-- The inverse of the flat derived-tensor comparison. -/
  flatDerivedTensorComparisonInv :
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r)) →
      ∀ (p : ℕ) (q : ℤ), gaussManinExactTensorHomologyTerm q hFlat p ⟶
        relativePageOneTerm f b p q
  /-- The two flat derived-tensor comparison maps are inverse in the forward order. -/
  flatDerivedTensorComparison_hom_inv :
    ∀ (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
      (p : ℕ) (q : ℤ),
      flatDerivedTensorComparison hFlat p q ≫
        flatDerivedTensorComparisonInv hFlat p q = 𝟙 _
  /-- The two flat derived-tensor comparison maps are inverse in the reverse order. -/
  flatDerivedTensorComparison_inv_hom :
    ∀ (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
      (p : ℕ) (q : ℤ),
      flatDerivedTensorComparisonInv hFlat p q ≫
        flatDerivedTensorComparison hFlat p q = 𝟙 _
  /-- The page-one chain action induced by the relative cup product and wedge product. -/
  relativeCupProductMap : ∀ q : ℤ,
    HomologicalComplex.tensorObj (E.pageOneRow q)
      (gaussManinDeRhamDGA b).toComplex ⟶ E.pageOneRow q
  /-- The source-level action on the derived-tensor presentation, obtained from
  `RelativeCupProduct.map` followed by the image of `extendedWedge`. -/
  relativeCupProductTermAction : ∀ (q : ℤ) (p m : ℕ),
    relativePageOneTerm f b p q ⊗ (gaussManinDeRhamDGA b).toComplex.X (m : ℤ) ⟶
      relativePageOneTerm f b (p + m) q
  /-- The page-one action is associative with the relative wedge product. -/
  relativeCupProductMap_assoc : ∀ (q n m k : ℤ),
    (α_ ((E.pageOneRow q).X n) ((gaussManinDeRhamDGA b).toComplex.X m)
          ((gaussManinDeRhamDGA b).toComplex.X k)).hom ≫
        ((E.pageOneRow q).X n ◁ (gaussManinDeRhamDGA b).mul m k) ≫
        HomologicalComplex.Monoidal.tensorHomComponent
          (relativeCupProductMap q) n (m + k) =
      (HomologicalComplex.Monoidal.tensorHomComponent
          (relativeCupProductMap q) n m ▷
            (gaussManinDeRhamDGA b).toComplex.X k) ≫
        HomologicalComplex.Monoidal.tensorHomComponent
          (relativeCupProductMap q) (n + m) k ≫
        eqToHom (congrArg (E.pageOneRow q).X (Int.add_assoc n m k))
  /-- The relative de Rham unit acts identically on the page-one row. -/
  relativeCupProductMap_one : ∀ (q n : ℤ),
    (ρ_ ((E.pageOneRow q).X n)).hom =
      ((E.pageOneRow q).X n ◁ (gaussManinDeRhamDGA b).one) ≫
        HomologicalComplex.Monoidal.tensorHomComponent
          (relativeCupProductMap q) n 0 ≫
        eqToHom (congrArg (E.pageOneRow q).X (add_zero n))

namespace CupWedge

/-- The Künneth forward map is the flat derived-tensor comparison followed by exact tensor
commuting with homology. -/
noncomputable def kunnethHom {X Y S : Scheme.{u}} {f : X ⟶ Y} {b : Y ⟶ S}
    [hPush : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u, u, u, u} (coefficientSite f))]
    [hRestr : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (scalarRestrictionHom b))
      (ModuleQis.{u, u, u, u} (coefficientSite (𝟙 Y)))]
    [hTensor : @DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
        (coefficientSite (𝟙 Y))) _ _ _ _ _ _ _]
    {E : CohomologicalSpectralSequence
      (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite b)) 0}
    (C : CupWedge f b E)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (p : ℕ) (q : ℤ) :
    relativePageOneTerm f b p q ⟶ gaussManinTerm f b p q :=
  C.flatDerivedTensorComparison hFlat p q ≫
    (gaussManinExactTensorHomologyIso q hFlat p).hom

/-- The Künneth inverse map reverses the exact-tensor/homology and flat derived-tensor
comparisons. -/
noncomputable def kunnethInv {X Y S : Scheme.{u}} {f : X ⟶ Y} {b : Y ⟶ S}
    [hPush : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u, u, u, u} (coefficientSite f))]
    [hRestr : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (scalarRestrictionHom b))
      (ModuleQis.{u, u, u, u} (coefficientSite (𝟙 Y)))]
    [hTensor : @DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
        (coefficientSite (𝟙 Y))) _ _ _ _ _ _ _]
    {E : CohomologicalSpectralSequence
      (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite b)) 0}
    (C : CupWedge f b E)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (p : ℕ) (q : ℤ) :
    gaussManinTerm f b p q ⟶ relativePageOneTerm f b p q :=
  (gaussManinExactTensorHomologyIso q hFlat p).inv ≫
    C.flatDerivedTensorComparisonInv hFlat p q

end CupWedge
end RelativeSpectralSequence

/-- A relative de Rham spectral sequence together with concrete Künneth comparisons and a
cup–wedge enhancement. -/
structure RelativeSpectralSequence {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (a : X ⟶ S) (b : Y ⟶ S) (sq : CommSq f a b (𝟙 S))
    [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    [hPush : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u, u, u, u} (coefficientSite f))]
    [hRestr : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (scalarRestrictionHom b))
      (ModuleQis.{u, u, u, u} (coefficientSite (𝟙 Y)))]
    [hRelative : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (relativePushforwardHom sq))
      (ModuleQis.{u, u, u, u} (coefficientSite a))]
    [hTensor : @DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
        (coefficientSite (𝟙 Y))) _ _ _ _ _ _ _] where
  /-- The filtered complex whose spectral sequence is used. -/
  filtration : FilteredComplex (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite b))
  /-- The spectral sequence associated with `filtration`. -/
  spectralSequence : CohomologicalSpectralSequence
    (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite b)) 0
  /-- The explicit derived-tensor comparisons and cup–wedge maps on the first page. -/
  cupWedge : RelativeSpectralSequence.CupWedge f b spectralSequence
  /-- The chosen spectral sequence is associated with the filtered complex. -/
  associated : filtration.IsAssociated spectralSequence
  /-- The first page is identified with the derived relative tensor expression. -/
  pageOneIso : ∀ (p : ℕ) (q : ℤ),
    (spectralSequence.page 1 zero_le_one).X ((p : ℤ), q) ≅
      relativePageOneTerm f b p q
  /-- The page-one action agrees with the source-level relative cup–wedge action under the
  displayed page-one identifications. -/
  cupWedge_induced : ∀ (q : ℤ) (p m : ℕ),
    (((CohomologicalSpectralSequence.PageOneRow.xIso spectralSequence p q ≪≫
          pageOneIso p q).hom) ⊗ₘ 𝟙 _) ≫
        cupWedge.relativeCupProductTermAction q p m =
      HomologicalComplex.Monoidal.tensorHomComponent
          (cupWedge.relativeCupProductMap q) (p : ℤ) (m : ℤ) ≫
        (CohomologicalSpectralSequence.PageOneRow.xIso spectralSequence (p + m) q ≪≫
          pageOneIso (p + m) q).hom
  /-- The filtered-complex homology has the relative de Rham abutment. -/
  abutmentIso : ∀ n : ℤ,
    filtration.underlying.homology n ≅ relativeAbutment sq n
  /-- The spectral sequence is bounded. -/
  isBounded : spectralSequence.IsBounded
  /-- The spectral sequence converges to the filtered-complex homology. -/
  converges : Converges filtration spectralSequence

namespace RelativeSpectralSequence

/-- Bundle a relative de Rham spectral-sequence witness with an explicit `CupWedge` enhancement. -/
def ofLemmaWitness {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (a : X ⟶ S) (b : Y ⟶ S) (sq : CommSq f a b (𝟙 S))
    [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    [hPush : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u, u, u, u} (coefficientSite f))]
    [hRestr : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (scalarRestrictionHom b))
      (ModuleQis.{u, u, u, u} (coefficientSite (𝟙 Y)))]
    [hRelative : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (relativePushforwardHom sq))
      (ModuleQis.{u, u, u, u} (coefficientSite a))]
    [hTensor : @DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
        (coefficientSite (𝟙 Y))) _ _ _ _ _ _ _]
    (K : FilteredComplex (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite b)))
    (E : CohomologicalSpectralSequence
      (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite b)) 0)
    (cupWedge : CupWedge f b E)
    (associated : K.IsAssociated E)
    (pageOneIso : ∀ (p : ℕ) (q : ℤ),
      (E.page 1 zero_le_one).X ((p : ℤ), q) ≅ relativePageOneTerm f b p q)
    (cupWedge_induced : ∀ (q : ℤ) (p m : ℕ),
      (((CohomologicalSpectralSequence.PageOneRow.xIso E p q ≪≫
            pageOneIso p q).hom) ⊗ₘ 𝟙 _) ≫
          cupWedge.relativeCupProductTermAction q p m =
        HomologicalComplex.Monoidal.tensorHomComponent
            (cupWedge.relativeCupProductMap q) (p : ℤ) (m : ℤ) ≫
          (CohomologicalSpectralSequence.PageOneRow.xIso E (p + m) q ≪≫
            pageOneIso (p + m) q).hom)
    (abutmentIso : ∀ n : ℤ, K.underlying.homology n ≅ relativeAbutment sq n)
    (isBounded : E.IsBounded) (converges : Converges K E) :
    RelativeSpectralSequence f a b sq where
  filtration := K
  spectralSequence := E
  cupWedge := cupWedge
  associated := associated
  pageOneIso := pageOneIso
  cupWedge_induced := cupWedge_induced
  abutmentIso := abutmentIso
  isBounded := isBounded
  converges := converges

/-- The concrete flat Künneth and cup–wedge enhancement stored in a relative spectral sequence. -/
noncomputable def canonicalCupWedge {X Y S : Scheme.{u}}
    {f : X ⟶ Y} {a : X ⟶ S} {b : Y ⟶ S} {sq : CommSq f a b (𝟙 S)}
    [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    [hPush : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u, u, u, u} (coefficientSite f))]
    [hRestr : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (scalarRestrictionHom b))
      (ModuleQis.{u, u, u, u} (coefficientSite (𝟙 Y)))]
    [hRelative : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (relativePushforwardHom sq))
      (ModuleQis.{u, u, u, u} (coefficientSite a))]
    [hTensor : @DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
        (coefficientSite (𝟙 Y))) _ _ _ _ _ _ _]
    (D : RelativeSpectralSequence f a b sq) :
    CupWedge f b D.spectralSequence :=
  D.cupWedge

/-- The stored cup-wedge action agrees with its derived-tensor presentation under the
page-one comparison isomorphisms. -/
theorem cupWedge_spec {X Y S : Scheme.{u}}
    {f : X ⟶ Y} {a : X ⟶ S} {b : Y ⟶ S} {sq : CommSq f a b (𝟙 S)}
    [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    [hPush : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u, u, u, u} (coefficientSite f))]
    [hRestr : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (scalarRestrictionHom b))
      (ModuleQis.{u, u, u, u} (coefficientSite (𝟙 Y)))]
    [hRelative : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (relativePushforwardHom sq))
      (ModuleQis.{u, u, u, u} (coefficientSite a))]
    [hTensor : @DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
        (coefficientSite (𝟙 Y))) _ _ _ _ _ _ _]
    (D : RelativeSpectralSequence f a b sq) (q : ℤ) (p m : ℕ) :
    (((CohomologicalSpectralSequence.PageOneRow.xIso D.spectralSequence p q ≪≫
          D.pageOneIso p q).hom) ⊗ₘ 𝟙 _) ≫
        (canonicalCupWedge D).relativeCupProductTermAction q p m =
      HomologicalComplex.Monoidal.tensorHomComponent
          ((canonicalCupWedge D).relativeCupProductMap q) (p : ℤ) (m : ℤ) ≫
        (CohomologicalSpectralSequence.PageOneRow.xIso
          D.spectralSequence (p + m) q ≪≫ D.pageOneIso (p + m) q).hom := sorry

end RelativeSpectralSequence

/-- A smooth relative de Rham setup with flat cohomology sheaves admits a bounded
spectral sequence equipped with the Kunneth comparisons and cup-wedge action. -/
theorem existsGaussManinSpectralSequence {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (a : X ⟶ S) (b : Y ⟶ S) (sq : CommSq f a b (𝟙 S))
    [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    [hPush : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u, u, u, u} (coefficientSite f))]
    [hRestr : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (scalarRestrictionHom b))
      (ModuleQis.{u, u, u, u} (coefficientSite (𝟙 Y)))]
    [hRelative : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (relativePushforwardHom sq))
      (ModuleQis.{u, u, u, u} (coefficientSite a))]
    [hTensor : @DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
        (coefficientSite (𝟙 Y))) _ _ _ _ _ _ _]
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r)) :
    Nonempty (RelativeSpectralSequence f a b sq) := sorry


end AlgebraicGeometry.Scheme.DeRham
