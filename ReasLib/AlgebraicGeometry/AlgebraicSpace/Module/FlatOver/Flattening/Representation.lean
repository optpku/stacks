/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Flattening.Universal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Purity.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions.Implications

/-!
# Representability of universal flattenings

Relative purity gives universal flattenings for finitely presented modules along
finitely presented morphisms of algebraic spaces. Properness supplies relative purity.
The resulting flattening morphisms are monomorphisms of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.Flattening

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)

/-- A finitely presented module pure relative to the target of a finitely presented
morphism of algebraic spaces has a universal flattening. -/
theorem hasUniversalFlattening_of_isPureOver [FinitePresentation f]
    [ℱ.IsFinitePresentation] (h_pure : ℱ.IsPureOver f) :
    HasUniversalFlattening f ℱ :=
  sorry

/-- A finitely presented module on the source of a proper finitely presented morphism
of algebraic spaces has a universal flattening. -/
instance instIsAlgebraicSpace_of_isProper [Proper f] [FinitePresentation f]
    [ℱ.IsFinitePresentation] :
    IsAlgebraicSpace (overSFunctor f ℱ) :=
  sorry

/-- The universal flattening morphism of a finitely presented relatively pure module
along a finitely presented morphism is of finite presentation. -/
theorem finitePresentation_toY_of_isPureOver [FinitePresentation f]
    [ℱ.IsFinitePresentation] (h_pure : ℱ.IsPureOver f)
    [IsAlgebraicSpace (overSFunctor f ℱ)] :
    FinitePresentation (toY f ℱ) :=
  sorry

/-- The universal flattening morphism of a finitely presented module along a proper
finitely presented morphism is of finite presentation. -/
instance finitePresentation_toY_of_isProper [Proper f] [FinitePresentation f]
    [ℱ.IsFinitePresentation] [IsAlgebraicSpace (overSFunctor f ℱ)] :
    FinitePresentation (toY f ℱ) :=
  sorry

/-- The structural morphism of a representable ordinary flattening functor is a
monomorphism. -/
instance instMono_toY [ℱ.IsQuasicoherent] [IsAlgebraicSpace (overSFunctor f ℱ)] :
    Mono (toY f ℱ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.Flattening

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- A finitely presented morphism whose source is pure relative to the target has a
universal flattening of its source. -/
theorem hasUniversalFlattening_of_isPureOver [FinitePresentation f]
    (h_pure : IsPureOver f) : HasUniversalFlattening f :=
  sorry

/-- The universal flattening morphism of a relatively pure source along a finitely
presented morphism is of finite presentation. -/
theorem finitePresentation_toY_of_isPureOver [FinitePresentation f]
    (h_pure : IsPureOver f)
    [IsAlgebraicSpace
      (Modules.Flattening.overSFunctor f (SheafOfModules.unit (structureSheaf X)))] :
    FinitePresentation
      (Modules.Flattening.toY f (SheafOfModules.unit (structureSheaf X))) :=
  sorry

/-- A proper finitely presented morphism of algebraic spaces has a universal
flattening of its source. -/
instance instIsAlgebraicSpace_of_isProper [Proper f] [FinitePresentation f] :
    IsAlgebraicSpace
      (Modules.Flattening.overSFunctor f (SheafOfModules.unit (structureSheaf X))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
