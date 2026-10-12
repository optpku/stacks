/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_27_3_QuasiFinite
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation

/-!
# Zariski's Main Theorem, finite-presentation addendum

A quasi-finite separated morphism of algebraic spaces which is locally of finite
presentation, with quasi-compact quasi-separated target, factors as a
quasi-compact open immersion followed by a finite morphism of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Lemma 76.34.4: With notation and hypotheses as in Lemma 76.34.3, if `f` is
moreover locally of finite presentation, the factorization `X ⟶ T ⟶ Y` may be
chosen so that `j` is a quasi-compact open immersion and `π : T ⟶ Y` is finite
and of finite presentation. -/
@[stacks 0874]
theorem QuasiFinite.exists_openImmersion_finitePresentationFactorization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiFinite f] [Separated f] [LocallyOfFinitePresentation f]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    ∃ (T : AlgebraicSpace S) (j : X ⟶ T) (π : T ⟶ Y),
      QuasiCompact j ∧ IsOpenImmersion j ∧ IsFinite π ∧
        FinitePresentation π ∧ j ≫ π = f :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
