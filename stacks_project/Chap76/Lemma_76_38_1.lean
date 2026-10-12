/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_14_4_IdealSubobject
public import stacks_project.Chap67.Lemma_67_13_1_Correspondence
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap71.Definition_71_6_6_Sum

/-!
# Pushing finite type ideals along quasi-compact separated étale morphisms

On a quasi-compact quasi-separated algebraic space, a finite type quasi-coherent
ideal on the source of a quasi-compact separated étale morphism that avoids the
preimage of a quasi-compact open subspace is, after multiplying by another finite
type quasi-coherent ideal, the inverse image of a finite type quasi-coherent
ideal on the target that avoids the open subspace.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.38.1: Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. Let `φ : W ⟶ X` be a quasi-compact
separated étale morphism. Let `U ⊂ X` be a quasi-compact open subspace. Let
`I ⊂ 𝒪_W` be a finite type quasi-coherent sheaf of ideals such that
`V(I) ∩ φ⁻¹(U) = ∅`. Then there exists a finite type quasi-coherent sheaf of
ideals `J ⊂ 𝒪_X` such that `V(J) ∩ U = ∅`, and `φ⁻¹(J) 𝒪_W = I * I'` for some
finite type quasi-coherent ideal `I' ⊂ 𝒪_W`. -/
@[stacks 087B]
theorem exists_finiteTypeIdeal_mul_of_etale {S : Scheme.{u}}
    {W X : AlgebraicSpace S} [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (φ : W ⟶ X) [QuasiCompact φ] [Separated φ] [Etale φ]
    (U : OpenSubspace X) [IsQuasiCompact U.X] (I : IdealSubobject W)
    [IsQuasiCoherent I] [(I : W.Modules).IsFiniteType]
    (hI : Disjoint (ClosedSubspace.ofQuasiCoherentIdeal I).pointsSet
      (Points.map φ ⁻¹' U.pointsSet)) :
    ∃ (J : IdealSubobject X) (_ : IsQuasiCoherent J),
      (J : X.Modules).IsFiniteType ∧
        Disjoint (ClosedSubspace.ofQuasiCoherentIdeal J).pointsSet U.pointsSet ∧
          ∃ (I' : IdealSubobject W) (_ : IsQuasiCoherent I'),
            (I' : W.Modules).IsFiniteType ∧
              J.pullback φ = IdealSubobject.mul I I' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
