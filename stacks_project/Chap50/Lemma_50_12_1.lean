module

public import stacks_project.Chap50.Lemma_50_3_5_DerivedDeRham
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.RelativeSpectralSequence
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape
open DerivedCategory.DerivedTensor
open DerivedCategory.DerivedTensor.Bifunctor
open FilteredComplex.Cohomology.Convergence
open SheafOfModules.RingedSite RingedSite.Hom
open AlgebraicGeometry.Scheme.Modules.Kunneth

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/- Lemma 50.12.1: for a quasi-compact, quasi-separated, smooth morphism
`f : X ⟶ Y` over `S`, there is a bounded spectral sequence with
`E₁^{p,q} = H^q(Ω^p_{Y/S} ⊗ᴸ_{𝒪_Y} Rf_* Ω^•_{X/Y})` converging to
`R^{p+q}f_* Ω^•_{X/S}`. -/
@[stacks 0FMM] #check
  (AlgebraicGeometry.Scheme.DeRham.existsRelativeSpectralSequence :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (a : X ⟶ S) (b : Y ⟶ S)
      (sq : CommSq f a b (𝟙 S)) [QuasiCompact f] [QuasiSeparated f] [Smooth f]
      [hPush : Functor.HasRightDerivedFunctor
        (modulePushforwardToDerived.{u, u, u, u, u, u}
          (DerivedPushforward.pushforwardHom f))
        (ModuleQis.{u, u, u, u} (coefficientSite f))]
      [hRestr : Functor.HasRightDerivedFunctor
        (modulePushforwardToDerived.{u, u, u, u, u, u} (scalarRestrictionHom b))
        (ModuleQis.{u, u, u, u} (coefficientSite (𝟙 Y)))]
      [hRelative : Functor.HasRightDerivedFunctor
        (modulePushforwardToDerived.{u, u, u, u, u, u} (relativePushforwardHom sq))
        (ModuleQis.{u, u, u, u} (coefficientSite a))]
      [hTensor : @Has
        (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) _ _
        (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
          (coefficientSite (𝟙 Y))) _ _ _ _ _ _ _],
      ∃ (K : FilteredComplex
          (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite b)))
        (E : CohomologicalSpectralSequence
          (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite b)) 0)
        (associated : K.IsAssociated E)
        (pageOneIso : ∀ (p : ℕ) (q : ℤ),
          (E.page 1 zero_le_one).X ((p : ℤ), q) ≅
            @relativePageOneTerm X Y S f b p q hPush hRestr hTensor)
        (abutmentIso : ∀ n : ℤ,
          K.underlying.homology n ≅ @relativeAbutment X Y S f a b sq n hRelative),
        E.IsBounded ∧ Converges K E)

end AlgebraicGeometry.Scheme.DeRham
