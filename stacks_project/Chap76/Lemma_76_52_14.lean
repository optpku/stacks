/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_28_5
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap75.Lemma_75_25_7_GlobalSections
public import stacks_project.Chap76.Lemma_76_52_5_Tensor

/-!
# Relative perfectness from perfect tensor-global sections

If `X` is separated, of finite presentation, and flat over a ring `A` and `K` is in
`D_QCoh(𝒪_X)`, then perfectness of `RΓ(X, E ⊗ᴸ K)` in `D(A)` for every perfect `E`
implies that `K` is `Spec(A)`-perfect.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Lemma 76.52.14. Let `A` be a ring. Let `X` be an algebraic space separated, of
finite presentation, and flat over `A`. Let `K` in `D_QCoh(𝒪_X)`. If `RΓ(X, E ⊗ᴸ K)`
is perfect in `D(A)` for every perfect `E` in `D(𝒪_X)`, then `K` is `Spec(A)`-perfect. -/
@[stacks 0GFL]
theorem isPerfectRelativeTo_of_forall_tensor_globalSections_perfect
    {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [Separated (toBase X)] [FinitePresentation (toBase X)] [Flat (toBase X)]
    {K : ModuleDerived X} (hK : derivedQuasiCoherentModuleProperty X K)
    (h : ∀ E : ModuleDerived X, IsPerfect E →
      DerivedCategory.IsPerfect
        ((globalSectionsOver (toBase X)).obj (tensorObj E K))) :
    IsPerfectRelativeTo (toBase X) K :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
