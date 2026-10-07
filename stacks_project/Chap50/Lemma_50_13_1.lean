module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LerayHirsch
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSite.Hom RingedSite.Hom.DerivedAdjunction
open AlgebraicGeometry.Scheme.Modules.Kunneth
open scoped MonoidalCategory

universe u

/- Lemma 50.13.1: for a smooth proper morphism of schemes, relative de Rham classes
forming a basis on every residue-field fibre induce the Leray--Hirsch isomorphism. -/
@[stacks 0FMP] #check
  (AlgebraicGeometry.Scheme.DeRham.LerayHirsch.map_isIso :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsProper f]
      [Functor.HasRightDerivedFunctor
        (RingedSite.Hom.modulePushforwardToDerived.{u}
          (AlgebraicGeometry.Scheme.DeRham.DerivedPushforward.pushforwardHom f))
        (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
          ((AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace ⋙
            AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace).map f)))]
      [RingedSite.Hom.DerivedAdjunction.HasPair.{u}
        (AlgebraicGeometry.Scheme.DeRham.DerivedPushforward.pushforwardHom f)]
      {N : ℕ} (n : Fin N → ℕ)
      (ξ : ∀ i, (DerivedCategory.singleFunctor
          (RingedSite.ModuleCat.{u, u, u, u}
            (AlgebraicGeometry.Scheme.Modules.Kunneth.coefficientSite (𝟙 Y)))
          (n i : ℤ)).obj
            (𝟙_ (RingedSite.ModuleCat.{u, u, u, u}
              (AlgebraicGeometry.Scheme.Modules.Kunneth.coefficientSite (𝟙 Y)))) ⟶
          (RingedSite.Hom.modulePushforwardDerived.{u}
            (AlgebraicGeometry.Scheme.DeRham.DerivedPushforward.pushforwardHom f)).obj
            (AlgebraicGeometry.Scheme.DeRham.DerivedPushforward.derivedComplex f))
      [∀ y : Y, Functor.HasRightDerivedFunctor
        (RingedSite.Hom.modulePushforwardToDerived.{u}
          (AlgebraicGeometry.Scheme.DeRham.DerivedPushforward.pushforwardHom
            (f.fiberToSpecResidueField y)))
        (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
          ((AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace ⋙
            AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace).map
              (f.fiberToSpecResidueField y))))]
      [∀ y : Y, RingedSite.Hom.DerivedAdjunction.HasPair.{u}
        (AlgebraicGeometry.Scheme.DeRham.DerivedPushforward.pushforwardHom
          (f.fiberToSpecResidueField y))]
      (hξ : AlgebraicGeometry.Scheme.DeRham.LerayHirsch.IsFiberwiseBasis f n ξ),
    IsIso (AlgebraicGeometry.Scheme.DeRham.LerayHirsch.map f n ξ))
