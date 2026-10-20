/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Relative.GlobalSections
import StacksCheckRecall

/-!
# Relative pseudo-coherence from tensor-global sections

If `X` is separated of finite presentation over a ring `A` and `K` is in
`D_QCoh(𝒪_X)`, then pseudo-coherence of `RΓ(X, E ⊗ᴸ K)` in `D(A)` for every
pseudo-coherent `E` implies that `K` is pseudo-coherent relative to `A`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

/- Lemma 76.51.4. Let `A` be a ring. Let `X` be an algebraic space separated and of
finite presentation over `A`. Let `K` in `D_QCoh(𝒪_X)`. If `RΓ(X, E ⊗ᴸ K)` is
pseudo-coherent in `D(A)` for every pseudo-coherent `E` in `D(𝒪_X)`, then `K` is
pseudo-coherent relative to `A` in the sense of Definition 76.45.3. -/
@[stacks 0CTT] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.isPseudoCoherentOver_of_globalSectionsTensor :
    ∀ {A : Type u} [CommRing A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      [Separated (SchemeRealization.toBase X)]
      [FinitePresentation (SchemeRealization.toBase X)] (K : DerivedQCoh X),
    (∀ E : ModuleDerived X, IsPseudoCoherent X E →
      CategoryTheory.DerivedCategory.IsPseudoCoherent
        ((Modules.globalSectionsOver (SchemeRealization.toBase X)).obj (E ⊗ᴸ K.obj))) →
      ModuleDerived.IsPseudoCoherentOver (SchemeRealization.toBase X) K.obj)
