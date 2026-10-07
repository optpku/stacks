module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_5_6_Instances
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap75.Lemma_75_25_7_GlobalSections
public import stacks_project.Chap75.Theorem_75_14_7_Qcqs

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

/-- Lemma 75.25.7: for a quasi-compact and quasi-separated algebraic space `X` over a
ring `A` and `K` in `D⁻_QCoh(𝒪_X)`, if `RΓ(X, E ⊗^L K)` is pseudo-coherent in `D(A)`
for every perfect `E` in `D(𝒪_X)`, then the same holds for every pseudo-coherent `E`
in `D(𝒪_X)`. -/
@[stacks 0CWH]
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
