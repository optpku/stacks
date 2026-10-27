/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Flattening.Representation
import StacksCheckRecall

/-!
# Universal flattening under finite presentation, purity, and properness

The ordinary universal flattening exists for finitely presented relatively pure
modules, relatively pure spaces, and the corresponding proper cases. In the first
three cases its canonical morphism is a monomorphism of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 77.11.8: universal flattening for finitely presented relatively pure modules
and spaces, and for proper finitely presented morphisms. -/
@[stacks 0CX2] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.hasUniversalFlattening_of_isPureOver :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)
      [FinitePresentation f] [ℱ.IsFinitePresentation],
      ℱ.IsPureOver f → Modules.Flattening.HasUniversalFlattening f ℱ)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.finitePresentation_toY_of_isPureOver :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)
      [FinitePresentation f] [ℱ.IsFinitePresentation] (h_pure : ℱ.IsPureOver f)
      [IsAlgebraicSpace (Modules.Flattening.overSFunctor f ℱ)],
      FinitePresentation (Modules.Flattening.toY f ℱ))

#check
  (AlgebraicGeometry.AlgebraicSpace.hasUniversalFlattening_of_isPureOver :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [FinitePresentation f], IsPureOver f → HasUniversalFlattening f)

#check
  (AlgebraicGeometry.AlgebraicSpace.finitePresentation_toY_of_isPureOver :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [FinitePresentation f] (h_pure : IsPureOver f)
      [IsAlgebraicSpace
        (Modules.Flattening.overSFunctor f (SheafOfModules.unit (structureSheaf X)))],
      FinitePresentation
        (Modules.Flattening.toY f (SheafOfModules.unit (structureSheaf X))))

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.instIsAlgebraicSpace_of_isProper :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)
      [Proper f] [FinitePresentation f] [ℱ.IsFinitePresentation],
      IsAlgebraicSpace (Modules.Flattening.overSFunctor f ℱ))

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.finitePresentation_toY_of_isProper :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)
      [Proper f] [FinitePresentation f] [ℱ.IsFinitePresentation]
      [IsAlgebraicSpace (Modules.Flattening.overSFunctor f ℱ)],
      FinitePresentation (Modules.Flattening.toY f ℱ))

#check
  (AlgebraicGeometry.AlgebraicSpace.instIsAlgebraicSpace_of_isProper :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Proper f] [FinitePresentation f],
      IsAlgebraicSpace
        (Modules.Flattening.overSFunctor f (SheafOfModules.unit (structureSheaf X))))

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.instMono_toY :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)
      [ℱ.IsQuasicoherent] [IsAlgebraicSpace (Modules.Flattening.overSFunctor f ℱ)],
      Mono (Modules.Flattening.toY f ℱ))
