/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf

/-!
# Finite presentation of closed immersions of algebraic spaces

A closed immersion of algebraic spaces is of finite presentation exactly when
its associated kernel ideal sheaf is of finite type as an `𝒪_X`-module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.28.12: A closed immersion `i : Z ⟶ X` of algebraic spaces is of
finite presentation if and only if the associated quasi-coherent sheaf of
ideals `I = Ker(𝒪_X ⟶ i_* 𝒪_Z)` is of finite type as an `𝒪_X`-module. -/
@[stacks 084Q]
theorem finitePresentation_iff_idealSheaf_isFiniteType
    {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    FinitePresentation i ↔ (Hom.idealSheaf i).IsFiniteType :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
