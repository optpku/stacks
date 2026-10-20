/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.GaussManin.DifferentialGraded
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.GaussManin.SpectralSequence
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageOneRow

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open CategoryTheory.DerivedCategory
open SheafOfModules.RingedSite RingedSite.Hom
open AlgebraicGeometry.Scheme.Modules.Kunneth

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

-- Local instance justification (defeq pin): the exact-tensor homology comparison must use the same ringed-site derived-category owner as `relativePageOneTerm`.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

section

variable {X Y S : Scheme.{u}}
variable {f : X ⟶ Y} {a : X ⟶ S} {b : Y ⟶ S} {sq : CommSq f a b (𝟙 S)}
variable [QuasiCompact f] [QuasiSeparated f] [Smooth f]
variable [hPush : Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{u, u, u, u, u, u} (DerivedPushforward.pushforwardHom f))
  (ModuleQis.{u, u, u, u} (coefficientSite f))]
variable [hRestr : Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{u, u, u, u, u, u} (scalarRestrictionHom b))
  (ModuleQis.{u, u, u, u} (coefficientSite (𝟙 Y)))]
variable [hRelative : Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{u, u, u, u, u, u} (relativePushforwardHom sq))
  (ModuleQis.{u, u, u, u} (coefficientSite a))]
variable [hTensor : @DerivedTensor.Bifunctor.Has
  (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) _ _
  (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
    (coefficientSite (𝟙 Y))) _ _ _ _ _ _ _]

/-- The page-one cup-wedge chain action supplied by the multiplicative enhancement. -/
noncomputable def gaussManinRowAction
    (D : RelativeSpectralSequence f a b sq) (q : ℤ) :
    HomologicalComplex.tensorObj (D.spectralSequence.pageOneRow q)
        (gaussManinDeRhamDGA b).toComplex ⟶ D.spectralSequence.pageOneRow q :=
  (RelativeSpectralSequence.canonicalCupWedge D).relativeCupProductMap q

/-- The homogeneous component of the page-one cup-wedge action. -/
noncomputable abbrev gaussManinRowActionComponent
    (D : RelativeSpectralSequence f a b sq) (q n m : ℤ) :=
  HomologicalComplex.Monoidal.tensorHomComponent (gaussManinRowAction D q) n m

/-- The action on the chosen first-page row is the transport of the source-level action
induced by `RelativeCupProduct.map` and `extendedWedge`. -/
theorem gaussManinRowAction_induced
    (D : RelativeSpectralSequence f a b sq) (q : ℤ) (p m : ℕ) :
    (((CohomologicalSpectralSequence.PageOneRow.xIso D.spectralSequence p q ≪≫
          D.pageOneIso p q).hom) ⊗ₘ 𝟙 _) ≫
        (RelativeSpectralSequence.canonicalCupWedge D).relativeCupProductTermAction q p m =
      gaussManinRowActionComponent D q (p : ℤ) (m : ℤ) ≫
        (CohomologicalSpectralSequence.PageOneRow.xIso
            D.spectralSequence (p + m) q ≪≫ D.pageOneIso (p + m) q).hom := sorry

/-- The supplied flat Künneth forward and reverse maps compose to the identity. -/
theorem gaussManinKunnethHom_inv
    (D : RelativeSpectralSequence f a b sq)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (p : ℕ) (q : ℤ) :
    (RelativeSpectralSequence.canonicalCupWedge D).kunnethHom hFlat p q ≫
      (RelativeSpectralSequence.canonicalCupWedge D).kunnethInv hFlat p q = 𝟙 _ := sorry

/-- The supplied flat Künneth reverse and forward maps compose to the identity. -/
theorem gaussManinKunnethInv_hom
    (D : RelativeSpectralSequence f a b sq)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (p : ℕ) (q : ℤ) :
    (RelativeSpectralSequence.canonicalCupWedge D).kunnethInv hFlat p q ≫
      (RelativeSpectralSequence.canonicalCupWedge D).kunnethHom hFlat p q = 𝟙 _ := sorry

/-- The supplied flat Künneth isomorphism, with both maps supplied as concrete data and only
their inverse laws deferred. -/
noncomputable def gaussManinKunnethIso
    (D : RelativeSpectralSequence f a b sq)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (p : ℕ) (q : ℤ) :
  relativePageOneTerm f b p q ≅ gaussManinTerm f b p q where
  hom := (RelativeSpectralSequence.canonicalCupWedge D).kunnethHom hFlat p q
  inv := (RelativeSpectralSequence.canonicalCupWedge D).kunnethInv hFlat p q
  hom_inv_id := gaussManinKunnethHom_inv D hFlat p q
  inv_hom_id := gaussManinKunnethInv_hom D hFlat p q

/-- The supplied first-page cup–wedge action is associative. -/
theorem gaussManinRowAction_assoc
    (D : RelativeSpectralSequence f a b sq) (q n m k : ℤ) :
    (α_ ((D.spectralSequence.pageOneRow q).X n)
          ((gaussManinDeRhamDGA b).toComplex.X m)
          ((gaussManinDeRhamDGA b).toComplex.X k)).hom ≫
        ((D.spectralSequence.pageOneRow q).X n ◁
          (gaussManinDeRhamDGA b).mul m k) ≫
        gaussManinRowActionComponent D q n (m + k) =
      (gaussManinRowActionComponent D q n m ▷
          (gaussManinDeRhamDGA b).toComplex.X k) ≫
        gaussManinRowActionComponent D q (n + m) k ≫
        eqToHom (congrArg (D.spectralSequence.pageOneRow q).X
          (Int.add_assoc n m k)) := sorry

/-- The relative de Rham unit acts identically on the page-one row. -/
theorem gaussManinRowAction_one
    (D : RelativeSpectralSequence f a b sq) (q n : ℤ) :
    (ρ_ ((D.spectralSequence.pageOneRow q).X n)).hom =
      ((D.spectralSequence.pageOneRow q).X n ◁ (gaussManinDeRhamDGA b).one) ≫
        gaussManinRowActionComponent D q n 0 ≫
        eqToHom (congrArg (D.spectralSequence.pageOneRow q).X (add_zero n)) := sorry

/-- The first differential obeys the graded Leibniz rule for the supplied cup–wedge action. -/
theorem gaussManinRowAction_leibniz
    (D : RelativeSpectralSequence f a b sq) (q n m : ℤ) :
    gaussManinRowActionComponent D q n m ≫
        (D.spectralSequence.pageOneRow q).d (n + m) (n + m + 1) =
      (((D.spectralSequence.pageOneRow q).d n (n + 1)) ▷
          (gaussManinDeRhamDGA b).toComplex.X m) ≫
          gaussManinRowActionComponent D q (n + 1) m ≫
          eqToHom
            (congrArg (D.spectralSequence.pageOneRow q).X
              ((Int.add_assoc n 1 m).trans
                ((congrArg (fun p : ℤ ↦ n + p) (Int.add_comm 1 m)).trans
                  (Int.add_assoc n m 1).symm))) +
        n.negOnePow •
          (((D.spectralSequence.pageOneRow q).X n ◁
              (gaussManinDeRhamDGA b).toComplex.d m (m + 1)) ≫
            gaussManinRowActionComponent D q n (m + 1) ≫
            eqToHom
              (congrArg (D.spectralSequence.pageOneRow q).X
                (Int.add_assoc n m 1).symm)) := sorry

/-- The differential graded module on the selected page-one row. Its carrier and
cup–wedge action are concrete; only the algebraic laws are deferred. -/
noncomputable def gaussManinModule
    (D : RelativeSpectralSequence f a b sq) (q : ℤ) :
    @SheafOfModules.RingedSite.DifferentialGradedModule.{u, u, u}
      _ _ (Opens.grothendieckTopology Y) _ _ _
      (RingedSpace.DeRham.coefficients b.toLRSHom.toShHom)
      (gaussManinDeRhamDGA b) where
  toComplex := D.spectralSequence.pageOneRow q
  smul := gaussManinRowActionComponent D q
  smul_assoc := gaussManinRowAction_assoc D q
  one_smul := gaussManinRowAction_one D q
  d_smul := gaussManinRowAction_leibniz D q

/-- The module action is exactly the page-one action induced by the relative cup product and
the extended wedge multiplication. -/
theorem gaussManinModule_smul
    (D : RelativeSpectralSequence f a b sq) (q n m : ℤ) :
    (gaussManinModule D q).smul n m =
      HomologicalComplex.Monoidal.tensorHomComponent
        ((RelativeSpectralSequence.canonicalCupWedge D).relativeCupProductMap q) n m := sorry

/-- The first-page term identified with its underived Gauss–Manin tensor term. -/
noncomputable def gaussManinPageOneComparison
    (D : RelativeSpectralSequence f a b sq)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (p : ℕ) (q : ℤ) :
    (D.spectralSequence.page 1 zero_le_one).X ((p : ℤ), q) ≅
      gaussManinTerm f b p q :=
  D.pageOneIso p q ≪≫ gaussManinKunnethIso D hFlat p q

/-- The restricted page-one row entry identified with the corresponding tensor term. -/
noncomputable def gaussManinRowEntryIso
    (D : RelativeSpectralSequence f a b sq)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (q : ℤ) (p : ℕ) :
    (D.spectralSequence.pageOneRow q).X (p : ℤ) ≅ gaussManinTerm f b p q :=
  CohomologicalSpectralSequence.PageOneRow.xIso D.spectralSequence p q ≪≫
    gaussManinPageOneComparison D hFlat p q

/-- The action of a relative form on a displayed Gauss–Manin tensor term, obtained by
transporting the page-one cup–wedge action through the flat Künneth identifications. -/
noncomputable def gaussManinTermAction
    (D : RelativeSpectralSequence f a b sq)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (q : ℤ) (p m : ℕ) :
    gaussManinTerm f b p q ⊗ (gaussManinDeRhamDGA b).toComplex.X (m : ℤ) ⟶
      gaussManinTerm f b (p + m) q :=
  ((gaussManinRowEntryIso D hFlat q p).inv ⊗ₘ 𝟙 _) ≫
    gaussManinRowActionComponent D q (p : ℤ) (m : ℤ) ≫
    (gaussManinRowEntryIso D hFlat q (p + m)).hom

/-- The first-page differential transported through the supplied Künneth comparison. -/
noncomputable def gaussManinRowDifferential
    (D : RelativeSpectralSequence f a b sq)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (q : ℤ) (p : ℕ) :
    gaussManinTerm f b p q ⟶ gaussManinTerm f b (p + 1) q :=
  (gaussManinRowEntryIso D hFlat q p).inv ≫
    (D.spectralSequence.pageOneRow q).d (p : ℤ) (p + 1 : ℤ) ≫
    (gaussManinRowEntryIso D hFlat q (p + 1)).hom

/-- Consecutive transported first-page differentials compose to zero. -/
theorem gaussManinRowDifferential_sq
    (D : RelativeSpectralSequence f a b sq)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (q : ℤ) (p : ℕ) :
    gaussManinRowDifferential D hFlat q p ≫
      gaussManinRowDifferential D hFlat q (p + 1) = 0 := sorry

/-- The explicit nonnegative complex with terms
`Ω^p_{Y/S} ⊗_{𝒪_Y} H^q_{dR}(X/Y)` and transported first-page differentials. -/
noncomputable def gaussManinRowComplex
    (D : RelativeSpectralSequence f a b sq)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (q : ℤ) :
    CochainComplex (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite b)) ℕ :=
  CochainComplex.of (fun p ↦ gaussManinTerm f b p q)
    (gaussManinRowDifferential D hFlat q)
    (gaussManinRowDifferential_sq D hFlat q)

/-- The termwise Künneth comparisons commute with the nonnegative row differentials. -/
theorem gaussManinDeRhamComplexIso_comm
    (D : RelativeSpectralSequence f a b sq)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (q : ℤ) (i j : ℕ) (hij : (up ℕ).Rel i j) :
    (gaussManinRowEntryIso D hFlat q i).hom ≫
        (gaussManinRowComplex D hFlat q).d i j =
      ((gaussManinModule D q).toComplex.restriction embeddingUpNat).d i j ≫
        (gaussManinRowEntryIso D hFlat q j).hom := sorry

/-- The nonnegative de Rham complex of the canonical Gauss–Manin module is the explicit
tensor-term complex with its transported first-page differentials. -/
noncomputable def gaussManinDeRhamComplexIso
    (D : RelativeSpectralSequence f a b sq)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (q : ℤ) :
    (gaussManinModule D q).toComplex.restriction embeddingUpNat ≅
      gaussManinRowComplex D hFlat q :=
  HomologicalComplex.Hom.isoOfComponents
    (gaussManinRowEntryIso D hFlat q)
    (gaussManinDeRhamComplexIso_comm D hFlat q)

/-- The canonical inclusion
`H^q_{dR}(X/Y) ⟶ Ω⁰_{Y/S} ⊗ H^q_{dR}(X/Y)` after restriction of scalars. -/
noncomputable def gaussManinFormZeroInclusion (q : ℤ) :
    restrictedRelativeDeRhamCohomology f b q ⟶ gaussManinTerm f b 0 q :=
  (modulePushforward (scalarRestrictionHom b)).map
    ((@MonoidalCategoryStruct.leftUnitor
        (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) _
        (moduleMonoidalCategory
          (RingedSpace.DeRham.coefficients (𝟙 Y.toRingedSpace))).toMonoidalCategoryStruct
        (relativeDeRhamCohomology f q)).inv ≫
      (relativeFormZeroUnit b ▷ relativeDeRhamCohomology f q))

/-- The degree-zero transported first-page differential, precomposed with the unit inclusion. -/
noncomputable def gaussManinConnectionMap
    (D : RelativeSpectralSequence f a b sq)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (q : ℤ) :
    restrictedRelativeDeRhamCohomology f b q ⟶ gaussManinTerm f b 1 q :=
  gaussManinFormZeroInclusion q ≫ gaussManinRowDifferential D hFlat q 0

/-- The canonical action of a relative `m`-form on relative de Rham cohomology, with the
cohomology sheaf inserted as the degree-zero Gauss–Manin term. -/
noncomputable def gaussManinConnectionAction
    (D : RelativeSpectralSequence f a b sq)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (q : ℤ) (m : ℕ) :
    restrictedRelativeDeRhamCohomology f b q ⊗
        (gaussManinDeRhamDGA b).toComplex.X (m : ℤ) ⟶
      gaussManinTerm f b m q :=
  (gaussManinFormZeroInclusion q ▷
      (gaussManinDeRhamDGA b).toComplex.X (m : ℤ)) ≫
    gaussManinTermAction D hFlat q 0 m ≫
    eqToHom (congrArg (fun p ↦ gaussManinTerm f b p q) (Nat.zero_add m))

/-- The Gauss–Manin connection is the degree-zero page-one differential. -/
theorem gaussManinConnectionMap_eq_pageOneDifferential
    (D : RelativeSpectralSequence f a b sq)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (q : ℤ) :
    gaussManinConnectionMap D hFlat q = gaussManinFormZeroInclusion q ≫
      (gaussManinRowEntryIso D hFlat q 0).inv ≫
      (D.spectralSequence.pageOneRow q).d 0 1 ≫
      (gaussManinRowEntryIso D hFlat q 1).hom := sorry

/-- Integrability of the Gauss–Manin connection: its first two transported differentials
compose to zero. -/
theorem gaussManinConnectionMap_integrable
    (D : RelativeSpectralSequence f a b sq)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (q : ℤ) :
    gaussManinConnectionMap D hFlat q ≫
      gaussManinRowDifferential D hFlat q 1 = 0 := sorry

/-- The Gauss–Manin connection satisfies the ordinary Leibniz identity for the canonical
right action of degree-zero relative forms. -/
theorem gaussManinConnectionMap_leibniz
    (D : RelativeSpectralSequence f a b sq)
    (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
    (q : ℤ) :
    gaussManinConnectionAction D hFlat q 0 ≫
        gaussManinRowDifferential D hFlat q 0 =
      (gaussManinConnectionMap D hFlat q ▷
          (gaussManinDeRhamDGA b).toComplex.X 0) ≫
          gaussManinTermAction D hFlat q 1 0 +
        (restrictedRelativeDeRhamCohomology f b q ◁
            (gaussManinDeRhamDGA b).toComplex.d 0 1) ≫
          gaussManinConnectionAction D hFlat q 1 := sorry

end

end AlgebraicGeometry.Scheme.DeRham
