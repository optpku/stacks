/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Generated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.RiemannRoch

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A proper morphism of reduced Gorenstein one-dimensional schemes over a field that preserves
the structure sheaf and has vanishing first higher direct image pulls back the target dualizing
module isomorphically when a positive tensor power of the source dualizing module is globally
generated and has vanishing first cohomology.

The positivity condition corrects the unrestricted integer exponent in Stacks tag 0E7P:
the argument using a tensor power of the comparison map requires a positive exponent. -/
theorem curveDualizingModule_pullback_isomorphic
    {k : Type u} [Field k] (X Y : SchemeOverField k) (c : X ⟶ Y)
    [IsProper X.hom] [IsProper Y.hom] [IsReduced X.left] [IsReduced Y.left]
    [Scheme.Gorenstein X.left] [Scheme.Gorenstein Y.left]
    [EquidimensionalSpace X.left] [EquidimensionalSpace Y.left]
    [Fact (topologicalKrullDim X.left = 1)] [Fact (topologicalKrullDim Y.left = 1)]
    (h_structure :
      IsIso (RingedSpace.Hom.commRingSheafPushforwardMap c.left.toShHom))
    (h_R1 :
      IsZero (RingedSpace.Hom.higherDirectImageModule c.left.toShHom
        (SheafOfModules.unit X.left.ringCatSheaf) 1))
    (h_power :
      ∃ m : ℤ, 0 < m ∧
        IsZero (Scheme.Hom.cohomology X.hom
          (Scheme.Modules.tensorPowerInt (curveDualizingModule X.hom) m) 1) ∧
          SheafOfModules.IsGloballyGenerated
            (Scheme.Modules.tensorPowerInt (curveDualizingModule X.hom) m)) :
    IsIsomorphic
      ((Scheme.Modules.pullback c.left).obj (curveDualizingModule Y.hom))
      (curveDualizingModule X.hom) := sorry

end AlgebraicGeometry.SchemeOverField

end
