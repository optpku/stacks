module

public import stacks_project.Chap73.Definition_73_9_1_FpqcCovering
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap75.Lemma_75_26_4_Pullback

/-!
# Fpqc descent of m-pseudo-coherence on algebraic spaces

An object of `D_QCoh(𝒪_X)` is `m`-pseudo-coherent if and only if each derived
pullback along an fpqc covering of `X` is `m`-pseudo-coherent.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.54.1: Let `S` be a scheme. Let `{f_i : X_i ⟶ X}` be an fpqc covering
of algebraic spaces over `S`. Let `E` in `D_QCoh(𝒪_X)`. Let `m` in `ℤ`. Then `E`
is `m`-pseudo-coherent if and only if each `Lf_i^* E` is `m`-pseudo-coherent,
where `Lf_i^*` is `modulePullbackDerived (family i).hom`. -/
@[stacks 0DL1]
theorem isMPseudoCoherent_iff_fpqcCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} (family : ι → Over X) (hfamily : FpqcCovering family)
    (E : ModuleDerived X) (hE : derivedQuasiCoherentModuleProperty X E) (m : ℤ) :
    IsMPseudoCoherent X E m ↔
      ∀ i, IsMPseudoCoherent (family i).left
        ((modulePullbackDerived (family i).hom).obj E) m :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
