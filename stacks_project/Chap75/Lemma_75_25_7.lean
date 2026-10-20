/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.GlobalSections
import StacksCheckRecall

/-!
# Perfect complexes detect pseudo-coherence of derived global sections

If `RΓ(X, E ⊗^L K)` is pseudo-coherent in `D(A)` for every perfect `E`, then the
same holds for every pseudo-coherent `E`, when `X` is qcqs over `A` and `K` is
bounded above with quasi-coherent cohomology.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open DerivedCategory.DerivedTensor DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/- Lemma 75.25.7: for a quasi-compact and quasi-separated algebraic space `X` over a
ring `A` and `K` in `D⁻_QCoh(𝒪_X)`, if `RΓ(X, E ⊗^L K)` is pseudo-coherent in `D(A)`
for every perfect `E` in `D(𝒪_X)`, then the same holds for every pseudo-coherent `E`
in `D(𝒪_X)`. -/
@[stacks 0CWH] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.globalSectionsTensor_isPseudoCoherent :
  ∀ {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (K : DerivedQCoh X)
    (hK_minus : (t.minus : ObjectProperty (ModuleDerived X)) K.obj)
    (hperfect :
      ∀ E : ModuleDerived X, ModuleDerived.IsPerfect E →
        ((Right.functor K.obj ⋙ Modules.globalSectionsOver f).obj E).IsPseudoCoherent)
    {E : ModuleDerived X} (hE : IsPseudoCoherent X E),
    ((Right.functor K.obj ⋙ Modules.globalSectionsOver f).obj E).IsPseudoCoherent)

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
