/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap68.Definition_68_3_1_FiberDegree
public import stacks_project.Chap69.Lemma_69_6_4_OffDiagonal
public import stacks_project.Chap69.Lemma_69_6_5_Quotient
public import stacks_project.Chap69.Situation_69_16_1_Cohomology

/-!
# Lemma 69.7.3

Existence of an affine étale atlas with a fibre-degree bound, together with
affine étale covers of the free quotients of the off-diagonal loci, and vanishing
of étale cohomology of quasi-coherent modules past `max (d_p + p)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 69.7.3 (1): if `X` is a quasi-compact quasi-separated algebraic space over
`S`, there exist an affine scheme `U`, a surjective étale morphism
`f : ofOver U ⟶ X`, an integer `d` with `degreesOfFibresBoundedBy f d`, and for
every `p : Fin (d + 1)` a free quotient `q p : offDiagonal f (p.val + 1) ⟶ Up p`
of `offDiagonalPermLift f (p.val + 1)` over `X` together with a surjective étale
morphism `g p : ofOver (Vp p) ⟶ Up p` from an affine scheme and an integer
`dp p` with `degreesOfFibresBoundedBy (g p) (dp p)`. -/
@[stacks 072C]
theorem exists_affineEtale_offDiagonalAffineCover
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    ∃ (U : Over S) (f : ofOver U ⟶ X) (d : ℕ),
      AlgebraicGeometry.IsAffine U.left ∧ Etale f ∧ Surjective f ∧ Separated f ∧
        degreesOfFibresBoundedBy f d ∧
        ∀ [Separated f],
          ∃ (Up : Fin (d + 1) → AlgebraicSpace S)
            (q : ∀ p, offDiagonal f (p.val + 1) ⟶ Up p)
            (π : ∀ p, Up p ⟶ X)
            (Vp : Fin (d + 1) → Over S)
            (g : ∀ p, ofOver (Vp p) ⟶ Up p)
            (dp : Fin (d + 1) → ℕ),
            (∀ p, IsFreeQuotient (offDiagonalPermLift f (p.val + 1)) (q p)) ∧
              (∀ p, Etale (π p)) ∧
              (∀ p, q p ≫ π p = offDiagonalToBase f (p.val + 1)) ∧
              (∀ p, AlgebraicGeometry.IsAffine (Vp p).left) ∧
              (∀ p, Etale (g p)) ∧ (∀ p, Surjective (g p)) ∧
              (∀ p, degreesOfFibresBoundedBy (g p) (dp p)) :=
  sorry

/-- Lemma 69.7.3 (2): given an affine étale surjection `f : ofOver U ⟶ X` with
`degreesOfFibresBoundedBy f d`, and for each `p : Fin (d + 1)` a free quotient
`q p : offDiagonal f (p.val + 1) ⟶ Up p` of `offDiagonalPermLift` over `X`
together with an affine étale surjection `g p : ofOver (Vp p) ⟶ Up p` with
`degreesOfFibresBoundedBy (g p) (dp p)`, every quasi-coherent `𝒪_X`-module `F`
satisfies `IsZero (cohomology X F n)` whenever `dp p + p.val ≤ n` for all `p`. -/
@[stacks 072C]
theorem cohomology_isZero_of_offDiagonalAffineCover
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    [AlgebraicGeometry.IsAffine U.left] (f : ofOver U ⟶ X)
    [Etale f] [Surjective f] [Separated f]
    (d : ℕ) (hd : degreesOfFibresBoundedBy f d)
    (Up : Fin (d + 1) → AlgebraicSpace S)
    (q : ∀ p, offDiagonal f (p.val + 1) ⟶ Up p)
    [∀ p, IsFreeQuotient (offDiagonalPermLift f (p.val + 1)) (q p)]
    (π : ∀ p, Up p ⟶ X) [∀ p, Etale (π p)]
    (hπ : ∀ p, q p ≫ π p = offDiagonalToBase f (p.val + 1))
    (Vp : Fin (d + 1) → Over S) [∀ p, AlgebraicGeometry.IsAffine (Vp p).left]
    (g : ∀ p, ofOver (Vp p) ⟶ Up p) [∀ p, Etale (g p)] [∀ p, Surjective (g p)]
    (dp : Fin (d + 1) → ℕ) (hdp : ∀ p, degreesOfFibresBoundedBy (g p) (dp p))
    (F : X.Modules) [F.IsQuasicoherent] {n : ℕ}
    (hn : ∀ p : Fin (d + 1), dp p + p.val ≤ n)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})] :
    IsZero (cohomology X F n) :=
  sorry

/-- A quasi-compact quasi-separated algebraic space has finite cohomological
dimension for quasi-coherent modules. -/
theorem exists_cohomology_isZero
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})] :
    ∃ n : ℕ, ∀ (F : X.Modules) [F.IsQuasicoherent] (q : ℕ),
      n ≤ q → IsZero (cohomology X F q) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
