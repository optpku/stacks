module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.MayerVietoris
import StacksCheckRecall


open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Functor CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

noncomputable section

universe u

variable {Y : Scheme.{u}} (X : Over Y) (P : Compactification.Of Y X)
variable (U V : X.left.Opens) (Λ : Type u) [CommRing Λ]
variable [hSeparated : IsSeparated X.hom] [hFiniteType : Scheme.Hom.FiniteType X.hom]
variable [hYCompact : CompactSpace Y] [hYQuasiSeparated : QuasiSeparatedSpace Y]
variable [hXCompact : CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [hUCompact : CompactSpace U] [hVCompact : CompactSpace V]
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ W : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over W) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ W : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over W) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ W : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over W) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [@Functor.Additive _ _ _ _ Abelian.toPreadditive Abelian.toPreadditive
  ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology)]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [HasSheafify U.toScheme.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ W : U.toScheme.Etale,
  HasWeakSheafify (U.toScheme.smallEtaleTopology.over W) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify V.toScheme.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ W : V.toScheme.Etale,
  HasWeakSheafify (V.toScheme.smallEtaleTopology.over W) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf V.toScheme.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify (U ⊓ V).toScheme.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ W : (U ⊓ V).toScheme.Etale,
  HasWeakSheafify ((U ⊓ V).toScheme.smallEtaleTopology.over W) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (U ⊓ V).toScheme.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : U.toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (U.ι)).op.HasLeftKanExtension F]
variable [∀ F : V.toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (V.ι)).op.HasLeftKanExtension F]
variable [∀ F : (U ⊓ V).toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction ((U ⊓ V).ι)).op.HasLeftKanExtension F]
variable [∀ F : (U ⊓ V).toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction ((X.left.homOfLE (inf_le_left : U ⊓ V ≤ U)))).op.HasLeftKanExtension F]
variable [∀ F : (U ⊓ V).toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction ((X.left.homOfLE (inf_le_right : U ⊓ V ≤ V)))).op.HasLeftKanExtension F]

variable [∀ F : U.toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (U.ι ≫ Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [∀ F : V.toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (V.ι ≫ Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [∀ F : (U ⊓ V).toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction ((U ⊓ V).ι ≫ Compactification.Of.ι P)).op.HasLeftKanExtension F]

variable [HasSheafCompose (smallEtaleTopology X.left)
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

set_option maxHeartbeats 1600000 in
/- Lemma 63.10.4. For a finite-type separated morphism of quasi-compact
quasi-separated schemes and a cover by two quasi-compact opens, derived lower
shriek gives the relative Mayer–Vietoris distinguished triangle, on bounded-below
torsion-cohomology complexes or on all complexes for torsion coefficients. -/
@[stacks 0GKN] #check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.mayerVietoris_triangle X P U V Λ :
    U ⊔ V = ⊤ →
    ∀ (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))),
      (AddMonoid.IsTorsion Λ ∨
        (etaleDerivedIsTorsion K ∧ ∃ n, DerivedCategory.IsGE K n)) →
    let hU : IsCompact (U : Set X.left) := isCompact_iff_compactSpace.mpr hUCompact
    let hV : IsCompact (V : Set X.left) := isCompact_iff_compactSpace.mpr hVCompact
    let hI : IsCompact (U ⊓ V : Set X.left) :=
      hU.inter_of_isOpen hV U.isOpen V.isOpen
    let eU := (openRestrictionIso X P U hU Λ).app
      ((etaleDerivedRestriction U.ι Λ).obj K)
    let eV := (openRestrictionIso X P V hV Λ).app
      ((etaleDerivedRestriction V.ι Λ).obj K)
    let eI := (openRestrictionIso X P (U ⊓ V) hI Λ).app
      ((etaleDerivedRestriction (U ⊓ V).ι Λ).obj K)
    let F_U := etaleDerivedExtensionByZeroRestrict U.ι Λ ⋙ etaleDerivedLowerShriek X P
    let F_V := etaleDerivedExtensionByZeroRestrict V.ι Λ ⋙ etaleDerivedLowerShriek X P
    ∃ δ,
      Triangle.mk
          (eI.inv ≫ (mayerVietorisToBiprod X P U V Λ).app K ≫
            Functor.biprodComparison ((CategoryTheory.evaluation
              (DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
              (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))).obj K) F_U F_V ≫
            (biprod.mapIso eU eV).hom)
          ((biprod.mapIso eU eV).inv ≫
            Functor.biprodComparison' ((CategoryTheory.evaluation
              (DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
              (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))).obj K) F_U F_V ≫
            (mayerVietorisFromBiprod X P U V Λ).app K) δ ∈
        distTriang (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))))

end
