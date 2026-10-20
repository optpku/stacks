/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped RelativeDerivation

universe u

/- The nodal-family property and its geometric consequences have canonical scheme owners. -/
#check (AlgebraicGeometry.AtWorstNodal : ∀ {X S : Scheme.{u}}, (X ⟶ S) → Prop)
#check (AlgebraicGeometry.atWorstNodal_iff :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S), AtWorstNodal f ↔
    SyntomicOfRelativeDimension f 1 ∧
      Unramified ((Scheme.fittingIdealSheaf (Ω[f.toShHom]) 1).subschemeι ≫ f))
#check (AlgebraicGeometry.AtWorstNodal.baseChange :
  ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S),
    [AtWorstNodal f] → AtWorstNodal (pullback.snd f g))
#check (AlgebraicGeometry.AtWorstNodal.relativeDimensionLE :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S), [AtWorstNodal f] → Scheme.Hom.RelativeDimensionLE f 1)
#check (AlgebraicGeometry.AtWorstNodal.geometricallyReduced :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S), [AtWorstNodal f] → GeometricallyReduced f)
