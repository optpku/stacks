module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem

@[expose] public section

/-!
# Localization Structure on Homotopy Quasi-Isomorphisms

@stack 05Q8

This leaf packages the localization structure carried by quasi-isomorphisms in an unbounded
homotopy category. The underlying quasi-isomorphism property and its shift compatibility are
owned by Mathlib; the saturation axiom and the resulting saturated multiplicative-system API live
here because they are useful to any triangulated localization argument, independently of a chosen
derived-category model.
-/

universe v u

open CategoryTheory
open CategoryTheory.MorphismProperty

open ComplexShape

namespace HomotopyCategory

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- quasi-isomorphisms in `K(C)` satisfy the intrinsic saturation axiom. -/
@[stacks 05Q8 "quasi-isomorphism saturation"]
instance quasiIso_hasSaturationAxiom :
    (quasiIso C (up ℤ)).HasSaturationAxiom := sorry

/-- quasi-isomorphisms in `K(C)` form a saturated multiplicative system. -/
@[stacks 05Q8 "quasi-isomorphism saturated multiplicative system"]
instance quasiIso_isSaturatedMultiplicativeSystem :
    (quasiIso C (up ℤ)).IsSaturatedMultiplicativeSystem := sorry

/-- Quasi-isomorphisms in `K(C)` are compatible with its triangulated structure. -/
@[stacks 05Q8 "quasi-isomorphism triangulated localization"]
instance quasiIso_isCompatibleWithTriangulation :
    (quasiIso C (up ℤ)).IsCompatibleWithTriangulation := sorry


end HomotopyCategory
