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

/-!
# Zariski's Main Theorem for algebraic spaces

A quasi-finite separated morphism of algebraic spaces over a scheme, with
quasi-compact quasi-separated target, factors as a quasi-compact open immersion
followed by a finite morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Lemma 76.34.3 (Zariski's Main Theorem): Let `S` be a scheme. Let `f : X ⟶ Y`
be a morphism of algebraic spaces over `S`. Assume `f` is quasi-finite and
separated and assume that `Y` is quasi-compact and quasi-separated. Then there
exists a factorization `X ⟶ T ⟶ Y` where `j : X ⟶ T` is a quasi-compact open
immersion and `π : T ⟶ Y` is finite. -/
@[stacks 082K]
theorem QuasiFinite.exists_openImmersion_finiteFactorization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiFinite f] [Separated f] [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    ∃ (T : AlgebraicSpace S) (j : X ⟶ T) (π : T ⟶ Y),
      QuasiCompact j ∧ IsOpenImmersion j ∧ IsFinite π ∧ j ≫ π = f :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
