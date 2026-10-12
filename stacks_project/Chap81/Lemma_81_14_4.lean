/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Topology.Sets.Closeds
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_29_5_Comparison
public import stacks_project.Chap67.Definition_67_39_1_Etale
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap71.Lemma_71_18_7_Blowup
public import stacks_project.Chap71.Lemma_71_18_7_Comparison
public import stacks_project.Chap72.Lemma_72_3_3_IsomorphismLocus

/-!
# Finite-flat quotients of étale local rings after admissible blowups

A proper morphism of qcqs algebraic spaces that is étale along a closed
subspace of a quasi-compact open, and an isomorphism onto its image there,
has, after a `V`-admissible blowup, a strict transform whose étale local
rings along the closure of that subspace admit a finite flat quotient from
the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 81.14.4. Let `S` be a scheme. Let `f : X ⟶ Y` be a proper morphism of
quasi-compact and quasi-separated algebraic spaces over `S`. Let `V ⊂ Y` be a
quasi-compact open and write `U = f⁻¹(V)` for `openInverseImage f V.ι`, so
`f|_U = openInverseImageTo f V.ι`. Let `A ⊂ U` and `B ⊂ V` be closed subspaces,
with `φ : A.X ⟶ B.X` the restriction `f|_A`, an isomorphism, and assume `f` is
étale at every point of `A`. Then there exists a `V`-admissible blowing up
`b : Y' ⟶ Y` such that the strict transform `f' : X' ⟶ Y'` satisfies: for every
geometric point `ā` of the closure of `|A|` in `|X'|` there exists an ideal `I`
of `etaleLocalRing X' ā` whose quotient map `Ideal.Quotient.mk I` realises a
quotient `𝒪_{X', ā} ⟶ 𝒪` for which the composite
`etaleLocalRing Y' (ā.map f') →+* 𝒪` is a finite flat local homomorphism
onto a nonzero quotient. -/
@[stacks 0F48]
theorem exists_isAdmissibleBlowup_strictTransform_finiteFlatStalkQuotient_near_closure
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) [Proper f]
    (V : OpenSubspace Y) [QuasiCompact V.ι]
    [IsQuasiCompact V.X] [IsAbsolutelyQuasiSeparated V.X]
    [IsQuasiCompact (openInverseImage f V.ι)]
    [IsAbsolutelyQuasiSeparated (openInverseImage f V.ι)]
    (A : ClosedSubspace (openInverseImage f V.ι))
    (B : ClosedSubspace V.X)
    [IsQuasiCompact A.X] [IsAbsolutelyQuasiSeparated A.X]
    [IsQuasiCompact B.X] [IsAbsolutelyQuasiSeparated B.X]
    (φ : A.X ⟶ B.X) [IsIso φ]
    (h_restrict : φ ≫ B.ι = A.ι ≫ openInverseImageTo f V.ι)
    (h_etale : ∀ a : Points A.X,
      EtaleAt f (Points.map (A.ι ≫ openInverseImageι f V.ι) a)) :
    ∃ (Y' : AlgebraicSpace S) (b : Y' ⟶ Y) (Z : ClosedSubspace Y)
      (h_blowup : IsBlowup b Z) (h_fp : FinitePresentation Z.ι)
      (h_disjoint : Disjoint Z.pointsSet V.pointsSet)
      (h_quasiCompact :
        QuasiCompact (strictTransformOpenComplement b (Z.inverseImage b) f).ι),
      let E := Z.inverseImage b
      ∀ (abar : GeometricPoint (strictTransform b E f).X),
        abar.image ∈
            closure
              (Points.map (strictTransformFst b E f) ⁻¹'
                Set.range (Points.map (A.ι ≫ openInverseImageι f V.ι))) →
          ∃ (I : Ideal (etaleLocalRing (strictTransform b E f).X abar)),
            let g := (Ideal.Quotient.mk I).comp
              (etaleLocalRingMap (strictTransformSnd b E f) abar)
            I ≠ ⊤ ∧ IsLocalHom g ∧ RingHom.Finite g ∧ RingHom.Flat g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
