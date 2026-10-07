module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Blowup.Triangle
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated RingedSite.Hom
open AlgebraicGeometry.Scheme.DeRham.Cohomology
open AlgebraicGeometry.IsBlowup
open AlgebraicGeometry.IsBlowup.DeRham
open RingedSite.Hom.DerivedAdjunction

/- Lemma 50.17.2 -/
@[stacks 0FUV] #check
  (@AlgebraicGeometry.IsBlowup.DeRham.exists_distinguishedTriangle :
    ∀ {S X X' : Scheme} (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X)
      [IsBlowup b I]
      [Functor.HasRightDerivedFunctor
        (modulePushforwardToDerived
          (coefficientHom (relativeStructureSquare f I b)))
        (ModuleQis (RingedSpace.DeRham.coefficientSite (b ≫ f).toLRSHom.toShHom))]
      [Functor.HasRightDerivedFunctor
        (modulePushforwardToDerived
          (coefficientHom (centerStructureSquare f I)))
        (ModuleQis
          (RingedSpace.DeRham.coefficientSite (I.subschemeι ≫ f).toLRSHom.toShHom))]
      [Functor.HasRightDerivedFunctor
        (modulePushforwardToDerived
          (coefficientHom (exceptionalInclusionStructureSquare f I b)))
        (ModuleQis (RingedSpace.DeRham.coefficientSite
          (exceptionalProjection I b ≫ I.subschemeι ≫ f).toLRSHom.toShHom))]
      [Functor.HasRightDerivedFunctor
        (modulePushforwardToDerived
          (coefficientHom (exceptionalStructureSquare f I b)))
        (ModuleQis (RingedSpace.DeRham.coefficientSite
          (exceptionalProjection I b ≫ I.subschemeι ≫ f).toLRSHom.toShHom))]
      [Functor.HasRightDerivedFunctor
        (modulePushforwardToDerived
          ((coefficientHom (exceptionalInclusionStructureSquare f I b)).comp
            (coefficientHom (relativeStructureSquare f I b))))
        (ModuleQis (RingedSpace.DeRham.coefficientSite
          (exceptionalProjection I b ≫ I.subschemeι ≫ f).toLRSHom.toShHom))]
      [Functor.HasRightDerivedFunctor
        (modulePushforwardToDerived
          ((coefficientHom (exceptionalStructureSquare f I b)).comp
            (coefficientHom (centerStructureSquare f I))))
        (ModuleQis (RingedSpace.DeRham.coefficientSite
          (exceptionalProjection I b ≫ I.subschemeι ≫ f).toLRSHom.toShHom))]
      [((coefficientHom
          (exceptionalInclusionStructureSquare f I b)).modulePushforward).IsRightAdjoint]
      [((coefficientHom
          (relativeStructureSquare f I b)).modulePushforward).IsRightAdjoint]
      [((coefficientHom
          (exceptionalStructureSquare f I b)).modulePushforward).IsRightAdjoint]
      [((coefficientHom
          (centerStructureSquare f I)).modulePushforward).IsRightAdjoint]
      [Functor.HasLeftDerivedFunctor
        (modulePullbackToDerived
          (coefficientHom (exceptionalInclusionStructureSquare f I b)))
        (ModuleQis (RingedSpace.DeRham.coefficientSite (b ≫ f).toLRSHom.toShHom))]
      [Functor.HasLeftDerivedFunctor
        (modulePullbackToDerived
          (coefficientHom (relativeStructureSquare f I b)))
        (ModuleQis (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))]
      [Functor.HasLeftDerivedFunctor
        (modulePullbackToDerived
          ((coefficientHom (exceptionalInclusionStructureSquare f I b)).comp
            (coefficientHom (relativeStructureSquare f I b))))
        (ModuleQis (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))]
      [Functor.HasLeftDerivedFunctor
        (modulePullbackToDerived
          (coefficientHom (exceptionalStructureSquare f I b)))
        (ModuleQis
          (RingedSpace.DeRham.coefficientSite (I.subschemeι ≫ f).toLRSHom.toShHom))]
      [Functor.HasLeftDerivedFunctor
        (modulePullbackToDerived
          (coefficientHom (centerStructureSquare f I)))
        (ModuleQis (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))]
      [Functor.HasLeftDerivedFunctor
        (modulePullbackToDerived
          ((coefficientHom (exceptionalStructureSquare f I b)).comp
            (coefficientHom (centerStructureSquare f I))))
        (ModuleQis (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))]
      [DerivedAdjunction.HasPair
        (coefficientHom (exceptionalInclusionStructureSquare f I b))]
      [DerivedAdjunction.HasPair
        (coefficientHom (relativeStructureSquare f I b))]
      [DerivedAdjunction.HasPair
        ((coefficientHom (exceptionalInclusionStructureSquare f I b)).comp
          (coefficientHom (relativeStructureSquare f I b)))]
      [DerivedAdjunction.HasPair
        (coefficientHom (exceptionalStructureSquare f I b))]
      [DerivedAdjunction.HasPair
        (coefficientHom (centerStructureSquare f I))]
      [DerivedAdjunction.HasPair
        ((coefficientHom (exceptionalStructureSquare f I b)).comp
          (coefficientHom (centerStructureSquare f I)))]
      [IsIso (modulePullbackDerived.compComparison
        (coefficientHom (exceptionalInclusionStructureSquare f I b))
        (coefficientHom (relativeStructureSquare f I b)))]
      [IsIso (modulePullbackDerived.compComparison
        (coefficientHom (exceptionalStructureSquare f I b))
        (coefficientHom (centerStructureSquare f I)))]
      [Smooth f] [Smooth (I.subschemeι ≫ f)],
      ∃ δ : (square f I b).shortComplex'.X₃ ⟶
          (square f I b).shortComplex'.X₁⟦(1 : ℤ)⟧,
        Triangle.mk (square f I b).shortComplex'.f
            (square f I b).shortComplex'.g δ ∈
          distTriang (RingedSite.Hom.ModuleDerived
            (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)))
