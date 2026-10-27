/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Functor
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.GerbeMorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-!
# The Picard stack as a gerbe over the relative Picard sheaf
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- For a flat proper finitely presented morphism whose structure-sheaf map
is universally an isomorphism, the canonical Picard classifying morphism is
a gerbe over the relative Picard sheaf for the fppf topology. -/
theorem toFunctor_isGerbeMorphism (f : X ⟶ B) [Flat f] [Proper f]
    [FinitePresentation f] [Hom.IsIsoBaseChangeStructurePushforward f] :
    CartesianBasedFunctor.IsGerbeMorphism (SchemesOver.fppfTopology B)
      (toFunctor f) := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
