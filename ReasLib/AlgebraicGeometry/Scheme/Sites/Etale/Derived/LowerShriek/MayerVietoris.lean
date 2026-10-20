module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.GroupTheory.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.OpenRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.MayerVietoris
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero.Exactness
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative Mayer–Vietoris triangle for derived étale lower shriek
-/


@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.Functor
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

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
section Maps

variable [HasWeakSheafify U.toScheme.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [Abelian (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ W : U.toScheme.Etale,
  HasWeakSheafify (U.toScheme.smallEtaleTopology.over W) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasWeakSheafify V.toScheme.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [Abelian (Sheaf V.toScheme.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ W : V.toScheme.Etale,
  HasWeakSheafify (V.toScheme.smallEtaleTopology.over W) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf V.toScheme.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasWeakSheafify (U ⊓ V).toScheme.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [Abelian (Sheaf (U ⊓ V).toScheme.smallEtaleTopology (ModuleCat.{u} Λ))]
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

namespace etaleDerivedLowerShriek

/-- The first relative Mayer–Vietoris map
`Rf_! (j_{U ∩ V!}((-) |_{U ∩ V})) ⟶ Rf_! (j_{U!}((-) |_U)) ⊞ Rf_! (j_{V!}((-) |_V))`,
obtained by whiskering the maps to each open with `etaleDerivedLowerShriek X P`
and lifting to the biproduct of images. -/
noncomputable def mayerVietorisToBiprod :
    etaleDerivedExtensionByZeroRestrict ((U ⊓ V).ι) Λ ⋙
        etaleDerivedLowerShriek X P ⟶
      (etaleDerivedExtensionByZeroRestrict (U.ι) Λ ⋙
          etaleDerivedLowerShriek X P) ⊞
        (etaleDerivedExtensionByZeroRestrict (V.ι) Λ ⋙
          etaleDerivedLowerShriek X P) :=
  biprod.lift
    (whiskerRight (mayerVietorisLowerShriekToLeft U V Λ)
      (etaleDerivedLowerShriek X P))
    (whiskerRight (mayerVietorisLowerShriekToRight U V Λ)
      (etaleDerivedLowerShriek X P))

/-- The second relative Mayer–Vietoris map
`Rf_! (j_{U!}((-) |_U)) ⊞ Rf_! (j_{V!}((-) |_V)) ⟶ Rf_!`, with a minus on the
`V`-component, obtained by descending the whiskered open-immersion counits. -/
noncomputable def mayerVietorisFromBiprod :
    (etaleDerivedExtensionByZeroRestrict (U.ι) Λ ⋙
        etaleDerivedLowerShriek X P) ⊞
      (etaleDerivedExtensionByZeroRestrict (V.ι) Λ ⋙
        etaleDerivedLowerShriek X P) ⟶
      etaleDerivedLowerShriek X P :=
  biprod.desc
    (whiskerRight (etaleDerivedExtensionByZeroAdjunction (U.ι) Λ).counit
        (etaleDerivedLowerShriek X P) ≫
      (Functor.leftUnitor (etaleDerivedLowerShriek X P)).hom)
    (whiskerRight (-(etaleDerivedExtensionByZeroAdjunction (V.ι) Λ).counit)
        (etaleDerivedLowerShriek X P) ≫
      (Functor.leftUnitor (etaleDerivedLowerShriek X P)).hom)

/-- The first projection of `mayerVietorisToBiprod` recovers the whiskered map
to the `U`-summand. -/
theorem mayerVietorisToBiprod_fst :
    mayerVietorisToBiprod X P U V Λ ≫ biprod.fst =
      whiskerRight (mayerVietorisLowerShriekToLeft U V Λ)
        (etaleDerivedLowerShriek X P) :=
  sorry

/-- The second projection of `mayerVietorisToBiprod` recovers the whiskered map
to the `V`-summand. -/
theorem mayerVietorisToBiprod_snd :
    mayerVietorisToBiprod X P U V Λ ≫ biprod.snd =
      whiskerRight (mayerVietorisLowerShriekToRight U V Λ)
        (etaleDerivedLowerShriek X P) :=
  sorry

/-- The left inclusion into `mayerVietorisFromBiprod` is `Rf_!` of the counit
along `U`. -/
theorem mayerVietorisFromBiprod_inl :
    biprod.inl ≫ mayerVietorisFromBiprod X P U V Λ =
      whiskerRight (etaleDerivedExtensionByZeroAdjunction (U.ι) Λ).counit
          (etaleDerivedLowerShriek X P) ≫
        (Functor.leftUnitor (etaleDerivedLowerShriek X P)).hom :=
  sorry

/-- The right inclusion into `mayerVietorisFromBiprod` is `Rf_!` of the negative
of the counit along `V`. -/
theorem mayerVietorisFromBiprod_inr :
    biprod.inr ≫ mayerVietorisFromBiprod X P U V Λ =
      whiskerRight (-(etaleDerivedExtensionByZeroAdjunction (V.ι) Λ).counit)
          (etaleDerivedLowerShriek X P) ≫
        (Functor.leftUnitor (etaleDerivedLowerShriek X P)).hom :=
  sorry

/-- The two relative Mayer–Vietoris maps compose to zero. -/
theorem mayerVietorisToBiprod_comp_fromBiprod :
    mayerVietorisToBiprod X P U V Λ ≫ mayerVietorisFromBiprod X P U V Λ = 0 :=
  sorry

end etaleDerivedLowerShriek

end Maps

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

namespace etaleDerivedLowerShriek

include hSeparated hFiniteType hYCompact hYQuasiSeparated hXCompact

section PlusTorsion

variable [HasSheafCompose (smallEtaleTopology X.left)
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

set_option maxHeartbeats 1600000 in
/-- For a separated finite-type morphism of quasi-compact quasi-separated
schemes covered by two quasi-compact opens, derived lower shriek gives the
Mayer–Vietoris distinguished triangle on bounded-below torsion-cohomology
complexes, and on all complexes for torsion coefficients. Its maps are the
canonical diagonal and difference maps transported to the restricted morphisms. -/
@[stacks 0GKN]
theorem mayerVietoris_triangle (hUV : U ⊔ V = ⊤) (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    (hK : AddMonoid.IsTorsion Λ ∨
      (etaleDerivedIsTorsion K ∧ ∃ n, DerivedCategory.IsGE K n)) :
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
        distTriang (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  sorry

set_option maxHeartbeats 1600000 in
/-- For a separated finite-type morphism of quasi-compact quasi-separated
schemes covered by two quasi-compact opens, derived lower shriek gives the relative
Mayer–Vietoris distinguished triangle for bounded-below complexes with torsion
cohomology. -/
theorem mayerVietoris_triangle_of_isGE_isTorsion (hUV : U ⊔ V = ⊤) {n : ℤ}
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) (h_tors : etaleDerivedIsTorsion K)
    [DerivedCategory.IsGE K n] :
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
        distTriang (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  sorry

end PlusTorsion

set_option maxHeartbeats 1600000 in
/-- For a separated finite-type morphism of quasi-compact quasi-separated
schemes covered by two quasi-compact opens and a torsion coefficient ring, derived
lower shriek gives the relative Mayer–Vietoris distinguished triangle for arbitrary
complexes. -/
theorem mayerVietoris_triangle_of_isTorsion (hΛ : AddMonoid.IsTorsion Λ)
    (hUV : U ⊔ V = ⊤) (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
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
        distTriang (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  sorry

end etaleDerivedLowerShriek

end AlgebraicGeometry.Scheme.Etale

end
