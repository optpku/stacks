/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Blowup.Triangle
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated RingedSite.Hom
open AlgebraicGeometry.Scheme.DeRham.Cohomology
open AlgebraicGeometry.IsBlowup
open AlgebraicGeometry.IsBlowup.DeRham
open RingedSite.Hom.DerivedAdjunction

universe u

variable {S X X' : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X)
  [IsBlowup b I]

variable
  [Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u}
      (coefficientHom (relativeStructureSquare f I b)))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite (b ≫ f).toLRSHom.toShHom))]
  [Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u}
      (coefficientHom (centerStructureSquare f I)))
    (ModuleQis.{u}
      (RingedSpace.DeRham.coefficientSite (I.subschemeι ≫ f).toLRSHom.toShHom))]
  [Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u}
      (coefficientHom (exceptionalInclusionStructureSquare f I b)))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
      (exceptionalProjection I b ≫ I.subschemeι ≫ f).toLRSHom.toShHom))]
  [Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u}
      (coefficientHom (exceptionalStructureSquare f I b)))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
      (exceptionalProjection I b ≫ I.subschemeι ≫ f).toLRSHom.toShHom))]
  [hExceptionalCompositeRight : Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u}
      ((coefficientHom (exceptionalInclusionStructureSquare f I b)).comp
        (coefficientHom (relativeStructureSquare f I b))))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
      (exceptionalProjection I b ≫ I.subschemeι ≫ f).toLRSHom.toShHom))]
  [hCenterCompositeRight : Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u}
      ((coefficientHom (exceptionalStructureSquare f I b)).comp
        (coefficientHom (centerStructureSquare f I))))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
      (exceptionalProjection I b ≫ I.subschemeι ≫ f).toLRSHom.toShHom))]
  [(RingedSite.Hom.modulePushforward.{u}
      (coefficientHom (exceptionalInclusionStructureSquare f I b))).IsRightAdjoint]
  [(RingedSite.Hom.modulePushforward.{u}
      (coefficientHom (relativeStructureSquare f I b))).IsRightAdjoint]
  [(RingedSite.Hom.modulePushforward.{u}
      (coefficientHom (exceptionalStructureSquare f I b))).IsRightAdjoint]
  [(RingedSite.Hom.modulePushforward.{u}
      (coefficientHom (centerStructureSquare f I))).IsRightAdjoint]
  [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{u}
      (coefficientHom (exceptionalInclusionStructureSquare f I b)))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite (b ≫ f).toLRSHom.toShHom))]
  [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{u}
      (coefficientHom (relativeStructureSquare f I b)))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))]
  [Functor.HasLeftDerivedFunctor
    (compositePullbackToDerived.{u}
      (coefficientHom (exceptionalInclusionStructureSquare f I b))
      (coefficientHom (relativeStructureSquare f I b)))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))]
  [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{u}
      (coefficientHom (exceptionalStructureSquare f I b)))
    (ModuleQis.{u}
      (RingedSpace.DeRham.coefficientSite (I.subschemeι ≫ f).toLRSHom.toShHom))]
  [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{u}
      (coefficientHom (centerStructureSquare f I)))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))]
  [Functor.HasLeftDerivedFunctor
    (compositePullbackToDerived.{u}
      (coefficientHom (exceptionalStructureSquare f I b))
      (coefficientHom (centerStructureSquare f I)))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))]
  [DerivedAdjunction.HasPair.{u}
    (coefficientHom (exceptionalInclusionStructureSquare f I b))]
  [DerivedAdjunction.HasPair.{u}
    (coefficientHom (relativeStructureSquare f I b))]
  [compositeDerivedPair.{u}
    (coefficientHom (exceptionalInclusionStructureSquare f I b))
    (coefficientHom (relativeStructureSquare f I b))
    (hCompositeRight := hExceptionalCompositeRight)]
  [DerivedAdjunction.HasPair.{u}
    (coefficientHom (exceptionalStructureSquare f I b))]
  [DerivedAdjunction.HasPair.{u}
    (coefficientHom (centerStructureSquare f I))]
  [compositeDerivedPair.{u}
    (coefficientHom (exceptionalStructureSquare f I b))
    (coefficientHom (centerStructureSquare f I))
    (hCompositeRight := hCenterCompositeRight)]
  [IsIso (modulePullbackDerived.compComparison.{u}
    (coefficientHom (exceptionalInclusionStructureSquare f I b))
    (coefficientHom (relativeStructureSquare f I b)))]
  [IsIso (modulePullbackDerived.compComparison.{u}
    (coefficientHom (exceptionalStructureSquare f I b))
    (coefficientHom (centerStructureSquare f I)))]
  [Smooth f] [Smooth (I.subschemeι ≫ f)]

/- Lemma 50.17.2 -/
@[stacks 0FUV] #check
  (AlgebraicGeometry.IsBlowup.DeRham.exists_distinguishedTriangle f I b :
    ∃ δ : (square f I b).shortComplex'.X₃ ⟶
        (square f I b).shortComplex'.X₁⟦(1 : ℤ)⟧,
      Triangle.mk (square f I b).shortComplex'.f
          (square f I b).shortComplex'.g δ ∈
        distTriang (RingedSite.Hom.ModuleDerived.{u}
          (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)))
