/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.Integral
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.Normal

/-!
# Normalization of connected finite étale covers

This module records integrality, generic-point behavior, and normalization comparison for a
connected finite étale morphism over a normal integral scheme.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.WeaklyEtale
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A connected finite étale morphism to a normal integral scheme has integral source. -/
theorem isIntegralOfFiniteEtaleOfConnected {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] (hX : X.isNormal) [IsFinite f] [Etale f] [ConnectedSpace Y] :
    IsIntegral Y := sorry

/-- A connected finite étale morphism over a normal integral scheme maps the generic point of its
source to the generic point of its target. -/
theorem mapGenericPoint_eq_of_finiteEtaleOfConnected
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIntegral X] (hX : X.isNormal)
    [IsFinite f] [Etale f] [ConnectedSpace Y] :
    -- Local instance justification (defeq pin): pin source integrality to the derived theorem so the generic point agrees with the normalization comparison.
    letI : IsIntegral Y := isIntegralOfFiniteEtaleOfConnected f hX
    f (genericPoint Y) = genericPoint X := sorry

/-- A connected finite étale cover of a normal integral scheme is its normalization in the source
function field. -/
theorem isIso_normalizationDescFunctionFieldExtension
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIntegral X] (hX : X.isNormal)
    [IsFinite f] [Etale f] [ConnectedSpace Y] :
    -- Local instance justification (defeq pin): use the derived integrality instance to identify the source function field and normalization comparison.
    letI : IsIntegral Y := isIntegralOfFiniteEtaleOfConnected f hX
    let h_generic := mapGenericPoint_eq_of_finiteEtaleOfConnected f hX
    let q := @Scheme.FunctionFieldExtension.map X _ Y.functionField _
      (f.functionFieldAlgebra h_generic)
    IsIso (q.normalizationDesc (Y.fromSpecStalk (genericPoint Y)) f
      (functionFieldExtensionMap_eq f h_generic)) := sorry

end AlgebraicGeometry.Scheme.Hom

end
