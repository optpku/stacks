/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.H
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Proper singleton h coverings

This module supplies h coverings arising from proper surjective morphisms of finite presentation.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.HCovering

/-- A surjective proper morphism of finite presentation, regarded as a singleton family, is an
h covering. -/
instance singletonOfProperSurjective {X Y : Scheme.{u}} (f : Y ⟶ X)
    [Surjective f] [IsProper f] [Hom.FinitePresentation f] :
    HCovering (fun _ : PUnit ↦ Over.mk f) := sorry

end AlgebraicGeometry.Scheme.HCovering
