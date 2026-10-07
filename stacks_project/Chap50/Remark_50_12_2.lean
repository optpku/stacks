module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.GaussManin.Connection
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.GaussManin.Finiteness
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open CategoryTheory.DerivedCategory
open AlgebraicGeometry.Scheme.Modules.Kunneth
open SheafOfModules.RingedSite RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

-- Local instance justification (defeq pin): the displayed exact-tensor comparison uses the ringed-site derived-category owner fixed by the relative page-one term.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

section

variable {X Y S : Scheme.{u}}
variable {f : X ⟶ Y} {a : X ⟶ S} {b : Y ⟶ S} {sq : CommSq f a b (𝟙 S)}
variable [QuasiCompact f] [QuasiSeparated f] [Smooth f] [IsProper f]
variable [S.Over (Spec (CommRingCat.of (ULift.{u} ℚ)))]
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
variable (D : RelativeSpectralSequence f a b sq)
variable (hFlat : ∀ r : ℤ, MonoidalCategory.IsFlat (relativeDeRhamCohomology f r))
variable (p : ℕ) (q : ℤ)

/- Remark 50.12.2 (1): relative de Rham cohomology is
`H^q(Rf_* Ω^•_{X/Y})`. -/
@[stacks 0FMN] #check
  (AlgebraicGeometry.Scheme.DeRham.relativeDeRhamCohomology f q :
    RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y)))

/- Remark 50.12.2 (2): proper smooth relative de Rham cohomology over a rational base is
finite locally free. -/
@[stacks 0FMN] #check
  (AlgebraicGeometry.Scheme.DeRham.relativeDeRhamCohomology_isFiniteLocallyFree
    f a b sq q : SheafOfModules.IsFiniteLocallyFree (relativeDeRhamCohomology f q))

/- Remark 50.12.2 (3): flatness identifies the `E₁` term with
`Ω^p_{Y/S} ⊗_{𝒪_Y} H^q_{dR}(X/Y)`. -/
@[stacks 0FMN] #check
  (AlgebraicGeometry.Scheme.DeRham.existsGaussManinSpectralSequence f a b sq hFlat :
    Nonempty (RelativeSpectralSequence f a b sq))

#check
  (AlgebraicGeometry.Scheme.DeRham.gaussManinPageOneComparison D hFlat p q :
    (D.spectralSequence.page 1 zero_le_one).X ((p : ℤ), q) ≅
      gaussManinTerm f b p q)

/- Remark 50.12.2 (4): the first-page differential gives
`d₁^{p,q} : Ω^p_{Y/S} ⊗ H^q_{dR}(X/Y) ⟶ Ω^{p+1}_{Y/S} ⊗ H^q_{dR}(X/Y)`. -/
@[stacks 0FMN] #check
  (AlgebraicGeometry.Scheme.DeRham.gaussManinRowDifferential D hFlat q p :
    gaussManinTerm f b p q ⟶ gaussManinTerm f b (p + 1) q)

/- Remark 50.12.2 (5): the Gauss-Manin connection is the degree-zero first-page differential
after the canonical inclusion by zero-forms. -/
@[stacks 0FMN] #check
  (AlgebraicGeometry.Scheme.DeRham.gaussManinConnectionMap_eq_pageOneDifferential D hFlat q :
    gaussManinConnectionMap D hFlat q = gaussManinFormZeroInclusion q ≫
      (gaussManinRowEntryIso D hFlat q 0).inv ≫
      (D.spectralSequence.pageOneRow q).d 0 1 ≫
      (gaussManinRowEntryIso D hFlat q 1).hom)

/- Remark 50.12.2 (6): the Gauss-Manin connection satisfies the Leibniz law. -/
@[stacks 0FMN] #check
  (AlgebraicGeometry.Scheme.DeRham.gaussManinConnectionMap_leibniz D hFlat q :
    gaussManinConnectionAction D hFlat q 0 ≫ gaussManinRowDifferential D hFlat q 0 =
      (gaussManinConnectionMap D hFlat q ▷
          (gaussManinDeRhamDGA b).toComplex.X 0) ≫
          gaussManinTermAction D hFlat q 1 0 +
        (restrictedRelativeDeRhamCohomology f b q ◁
            (gaussManinDeRhamDGA b).toComplex.d 0 1) ≫
          gaussManinConnectionAction D hFlat q 1)

/- Remark 50.12.2 (7): the Gauss-Manin connection is integrable. -/
@[stacks 0FMN] #check
  (AlgebraicGeometry.Scheme.DeRham.gaussManinConnectionMap_integrable D hFlat q :
    gaussManinConnectionMap D hFlat q ≫ gaussManinRowDifferential D hFlat q 1 = 0)

/- Remark 50.12.2 (8): the `d₁` row is the de Rham complex of the Gauss-Manin connection. -/
@[stacks 0FMN] #check
  (AlgebraicGeometry.Scheme.DeRham.gaussManinDeRhamComplexIso D hFlat q :
    (gaussManinModule D q).toComplex.restriction embeddingUpNat ≅
      gaussManinRowComplex D hFlat q)

end

end AlgebraicGeometry.Scheme.DeRham
