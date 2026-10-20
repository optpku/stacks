/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.OverField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open DerivedCategory.TStructure

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.OverField

/-- A derived module on an algebraic space of finite presentation over a field is
perfect relative to the field if and only if it is cohomologically bounded and
pseudo-coherent. -/
theorem isPerfectRelativeTo_iff_bounded_and_pseudoCoherent {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (.of k))) [FinitePresentation (SchemeRealization.toBase X)]
    (E : ModuleDerived X) :
    IsPerfectRelativeTo (SchemeRealization.toBase X) E ↔
      (t.bounded : ObjectProperty (ModuleDerived X)) E ∧ IsPseudoCoherent X E := sorry

/-- A derived module on an algebraic space of finite presentation over a field is
perfect relative to the field if and only if it is cohomologically bounded and has
coherent cohomology in every degree. -/
theorem isPerfectRelativeTo_iff_bounded_and_coherentCohomology {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (.of k))) [FinitePresentation (SchemeRealization.toBase X)]
    (E : ModuleDerived X) :
    IsPerfectRelativeTo (SchemeRealization.toBase X) E ↔
      (t.bounded : ObjectProperty (ModuleDerived X)) E ∧
        DerivedCategory.cohomologyIn (SheafOfModules.isCoherent (structureSheaf X)) E := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.OverField
