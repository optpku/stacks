/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.OverAffine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- If an algebraic space is separated and of finite presentation over an affine base and
the derived global sections of `E ⊗ᴸ K` are pseudo-coherent for every pseudo-coherent `E`,
then the quasi-coherent derived module `K` is pseudo-coherent relative to the base. -/
theorem isPseudoCoherentOver_of_globalSectionsTensor
    {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [Separated (SchemeRealization.toBase X)]
    [FinitePresentation (SchemeRealization.toBase X)] (K : DerivedQCoh X)
    (h : ∀ E : ModuleDerived X, IsPseudoCoherent X E →
      CategoryTheory.DerivedCategory.IsPseudoCoherent
        ((Modules.globalSectionsOver (SchemeRealization.toBase X)).obj (E ⊗ᴸ K.obj))) :
    ModuleDerived.IsPseudoCoherentOver (SchemeRealization.toBase X) K.obj := sorry

/-- If an algebraic space is separated and of finite presentation over an affine base and
the derived global sections of `E ⊗ᴸ K` are pseudo-coherent for every perfect `E`,
then the quasi-coherent derived module `K` is pseudo-coherent relative to the base. -/
theorem isPseudoCoherentOver_of_globalSectionsTensor_perfect
    {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [Separated (SchemeRealization.toBase X)]
    [FinitePresentation (SchemeRealization.toBase X)] (K : DerivedQCoh X)
    (h : ∀ E : ModuleDerived X, ModuleDerived.IsPerfect E →
      CategoryTheory.DerivedCategory.IsPseudoCoherent
        ((Modules.globalSectionsOver (SchemeRealization.toBase X)).obj (E ⊗ᴸ K.obj))) :
    ModuleDerived.IsPseudoCoherentOver (SchemeRealization.toBase X) K.obj := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
