module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Basic
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap75.«75_5_1_1_Comparison»
public import stacks_project.Chap75.Lemma_75_6_1_Pushforward
public import stacks_project.Chap75.Lemma_75_11_2_Coherator

/-!
# Étale affine pushforward criterion for the comparison on qcqs algebraic spaces

On a quasi-compact and quasi-separated algebraic space, commutativity of
K-injective quasi-coherent pushforward along étale morphisms from affine
spaces to quasi-compact opens with the comparisons `D(QCoh) ⥤ D_QCoh`
implies that the comparison is an equivalence with quasi-inverse the
restricted derived coherator.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Lemma 75.11.4. Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. Suppose that for every étale
morphism `j : V ⟶ W` with `W ⊂ X` quasi-compact open and `V` affine, the
right derived functor `QCoh.Derived.pushforward j` of
`j_* : QCoh 𝒪_V ⥤ QCoh 𝒪_W` fits into a commutative diagram with the
comparisons `comparison V` and `comparison W.X` against the restricted
ambient derived pushforward `pushforward j`. Then the functor
`comparison X` of 75.5.1.1 is an equivalence `D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)`
with quasi-inverse `inclusion X ⋙ QCoh.Derived.coherator X`. -/
@[stacks 09TG]
theorem comparison_isQuasiInverse {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (h_etalePushforward : ∀ {W : OpenSubspace X} {V : AlgebraicSpace S} (j : V ⟶ W.X)
      [Etale j] [IsQuasiCompact W.X] [IsAffine V] [QuasiCompact j] [QuasiSeparated j],
      IsIsomorphic (QCoh.Derived.pushforward j ⋙ comparison W.X)
        (comparison V ⋙ pushforward j)) :
    (comparison X).IsQuasiInverse (inclusion X ⋙ QCoh.Derived.coherator X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
