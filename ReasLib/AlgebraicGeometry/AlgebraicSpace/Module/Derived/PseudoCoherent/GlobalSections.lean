/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.OverAffine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Perfect complexes detect pseudo-coherence of derived global sections

For a bounded-above quasi-coherent derived module on a qcqs algebraic space,
pseudo-coherence of derived global sections after tensoring can be tested on
perfect complexes.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open DerivedCategory.DerivedTensor DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Let `X` be a quasi-compact and quasi-separated algebraic space over `A`, and let
`K` be a bounded-above derived module with quasi-coherent cohomology. If
`RΓ(X, E ⊗^L K)` is pseudo-coherent over `A` for every perfect `E`, then it is
pseudo-coherent over `A` for every pseudo-coherent `E`. -/
theorem globalSectionsTensor_isPseudoCoherent
    {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (K : DerivedQCoh X)
    (hK_minus : (t.minus : ObjectProperty (ModuleDerived X)) K.obj)
    (hperfect :
      ∀ E : ModuleDerived X, ModuleDerived.IsPerfect E →
        ((Right.functor K.obj ⋙ Modules.globalSectionsOver f).obj E).IsPseudoCoherent)
    {E : ModuleDerived X} (hE : IsPseudoCoherent X E) :
    ((Right.functor K.obj ⋙ Modules.globalSectionsOver f).obj E).IsPseudoCoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
