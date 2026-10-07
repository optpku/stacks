module

public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_28_5
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap75.Lemma_75_25_7_GlobalSections
public import stacks_project.Chap76.Lemma_76_45_4_Relative
public import stacks_project.Chap76.Lemma_76_52_5_Tensor

/-!
# Relative pseudo-coherence from perfect tensor-global sections

If `X` is separated of finite presentation over a ring `A` and `K` is in
`D_QCoh(𝒪_X)`, then pseudo-coherence of `RΓ(X, E ⊗ᴸ K)` in `D(A)` for every
perfect `E` implies that `K` is pseudo-coherent relative to `A`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Lemma 76.51.5. Let `A` be a ring. Let `X` be an algebraic space separated and of
finite presentation over `A`. Let `K` in `D_QCoh(𝒪_X)`. If `RΓ(X, E ⊗ᴸ K)` is
pseudo-coherent in `D(A)` for every perfect `E` in `D(𝒪_X)`, then `K` is
pseudo-coherent relative to `A`. -/
@[stacks 0GFJ]
theorem isPseudoCoherentOver_of_forall_tensor_globalSections_perfect
    {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [Separated (toBase X)] [FinitePresentation (toBase X)]
    {K : ModuleDerived X} (hK : derivedQuasiCoherentModuleProperty X K)
    (h : ∀ E : ModuleDerived X, IsPerfect E →
      CategoryTheory.DerivedCategory.IsPseudoCoherent
        ((globalSectionsOver (toBase X)).obj (tensorObj E K))) :
    IsPseudoCoherentOver (toBase X) K :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
