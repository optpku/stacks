/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.OverAffine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Relative perfectness from perfect tensor-global sections
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped CategoryTheory.DerivedCategory.DerivedTensor

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- A derived module with quasi-coherent cohomology on a separated, finitely presented,
flat algebraic space over `A` is perfect relative to `Spec A` if `RΓ(X, E ⊗ᴸ K)`
is perfect over `A` for every perfect derived module `E`. -/
theorem isPerfectRelativeTo_of_globalSectionsTensor
    {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [Separated (SchemeRealization.toBase X)]
    [FinitePresentation (SchemeRealization.toBase X)]
    [Flat (SchemeRealization.toBase X)]
    {K : ModuleDerived X} (hK : derivedQuasiCoherentModuleProperty X K)
    (h : ∀ E : ModuleDerived X, IsPerfect E →
      DerivedCategory.IsPerfect
        ((Modules.globalSectionsOver (SchemeRealization.toBase X)).obj (E ⊗ᴸ K))) :
    IsPerfectRelativeTo (SchemeRealization.toBase X) K := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
