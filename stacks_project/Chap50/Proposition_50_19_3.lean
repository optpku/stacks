/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Trace

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape TopologicalSpace
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

open TraceRule

/- Proposition 50.19.3: finite syntomic traces form an absolute de Rham complex map,
agree with the structure-sheaf trace in degree zero, preserve left wedge multiplication,
and induce compatible relative complex maps over every common base. -/
@[stacks 0FLC] #check (AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.complexMap :
  ∀ (r : TraceRule.{u}) (hr : IsTraceRule r)
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f],
    (RingedSpace.DeRham.pushforwardComplex (absoluteRingedSquare f)).obj
        (RingedSpace.DeRham.complex (terminal.from Y).toLRSHom.toShHom) ⟶
      RingedSpace.DeRham.complex (terminal.from X).toLRSHom.toShHom)

#check (AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.complexMap_f :
  ∀ (r : TraceRule.{u}) (hr : IsTraceRule r)
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f] (p : ℕ),
    (complexMap r hr f).f p = componentTerm r f p)

#check (AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.degreeZero :
  ∀ {r : TraceRule.{u}} (hr : IsTraceRule r)
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f],
    (complexMap r hr f).f 0 =
      (componentSourceIso f 0).hom ≫
        (DeRham.restriction
          (RingedSpace.DeRham.structureMap
            (terminal.from X).toLRSHom.toShHom)).map
          ((Scheme.Modules.toRingedSpace X).map
            ((Scheme.Modules.pushforward f).map
                  ((Scheme.Modules.fromRingedSpace Y).map
                    ((formExteriorIso (terminal.from Y) 0).hom ≫
                      (ExteriorPower.degreeZeroIso
                        Y.sheaf Ω[(terminal.from Y).toShHom]).hom)) ≫
              Scheme.Hom.finiteSyntomicTrace f ≫
              (Scheme.Modules.fromRingedSpace X).map
                ((ExteriorPower.degreeZeroIso
                    X.sheaf Ω[(terminal.from X).toShHom]).inv ≫
                  (formExteriorIso (terminal.from X) 0).inv))))

#check (AlgebraicGeometry.Scheme.RelativeDifferentials.IsTraceRule.wedge :
  ∀ {r : TraceRule.{u}} (hr : IsTraceRule r)
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f],
    TraceRule.IsWedgeLinear r f)

#check (AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.relativeComplexMap :
  ∀ (r : TraceRule.{u}) (hr : IsTraceRule r)
    {S X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f]
    (a : Y ⟶ S) (b : X ⟶ S) (sq : CommSq f a b (𝟙 S)),
    (RingedSpace.DeRham.pushforwardComplex (relativeRingedSquare sq)).obj
        (RingedSpace.DeRham.complex a.toLRSHom.toShHom) ⟶
      RingedSpace.DeRham.complex b.toLRSHom.toShHom)

#check (AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.relativeComplexMap_f :
  ∀ (r : TraceRule.{u}) (hr : IsTraceRule r)
    {S X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f]
    (a : Y ⟶ S) (b : X ⟶ S) (sq : CommSq f a b (𝟙 S)) (p : ℕ),
    (relativeComplexMap r hr f a b sq).f p =
      relativeComponent r hr f a b sq p)

#check (AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.relativeComplexMap_induced :
  ∀ (r : TraceRule.{u}) (hr : IsTraceRule r)
    {S X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f]
    (a : Y ⟶ S) (b : X ⟶ S) (sq : CommSq f a b (𝟙 S)) (p : ℕ),
    absoluteToRelativeSourceTerm f a b sq p ≫
        (SheafOfModules.toSheaf
          (TopCat.Sheaf.ringSheafOfComm
            (RingedSpace.DeRham.coefficients b.toLRSHom.toShHom))).map
          ((relativeComplexMap r hr f a b sq).f p) =
      (SheafOfModules.toSheaf
        (TopCat.Sheaf.ringSheafOfComm
          (RingedSpace.DeRham.coefficients
            (terminal.from X).toLRSHom.toShHom))).map
          ((complexMap r hr f).f p) ≫
        absoluteToRelativeTerm b p)

end AlgebraicGeometry.Scheme.RelativeDifferentials
