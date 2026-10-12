/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap69.Lemma_69_6_3
public import stacks_project.Chap69.Lemma_69_6_4
public import stacks_project.Chap69.Lemma_69_6_6_Character

/-!
# Lemma 69.6.6

The alternating Čech spectral sequence of a surjective étale separated morphism
of algebraic spaces has `E₁`-page given by cohomology of the sign-twisted
restriction to a free quotient of the off-diagonal locus, and converges to
the étale cohomology of `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Lemma 69.6.6 (1): Let `S` be a scheme. Let `f : U ⟶ X` be a surjective, étale,
and separated morphism of algebraic spaces over `S`. For `p ≥ 0` set
`W_p = offDiagonal f (p + 1)`. Let `χ_p = offDiagonalSignCharacter (p + 1)` be
the sign character of `S_{p+1}`. Let `q : W_p ⟶ U_p` be a free quotient of the
permutation action and `π : U_p ⟶ X` a morphism with
`q ≫ π = offDiagonalToBase f (p + 1)`. Then the spectral sequence of
Lemma 69.6.3 has `E₁`-page
`E₁^{p, n} ≅ H^n(U_p, F|_{U_p} ⊗_ℤ ℤ̲(χ_p))`. -/
@[stacks 0728]
theorem alternatingCechSpectralSequence_pageOne_characterTwist
    {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] [Surjective f] [Separated f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] (p : ℕ) {Up : AlgebraicSpace S}
    (q : offDiagonal f (p + 1) ⟶ Up)
    [IsFreeQuotient (offDiagonalPermLift f (p + 1)) q] (π : Up ⟶ X) [Etale π]
    (h_toBase : q ≫ π = offDiagonalToBase f (p + 1))
    [HasSheafify (smallEtaleTopology Up) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (smallEtaleTopology Up) AddCommGrpCat.{u + 1})]
    (n : ℕ) :
    IsIsomorphic (((alternatingCechSpectralSequence f F).page 1 le_rfl).X (p, n))
      ((Sheaf.functorH (smallEtaleTopology Up) n).obj
        (offDiagonalCharacterTwist f F p q π)) :=
  sorry

/-- Lemma 69.6.6 (2): Let `S` be a scheme. Let `f : U ⟶ X` be a surjective, étale,
and separated morphism of algebraic spaces over `S`. The spectral sequence of
Lemma 69.6.3 converges to `H^{p + n}(X, F)`. -/
@[stacks 0728]
theorem alternatingCechSpectralSequence_characterTwist_convergesTo
    {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] [Surjective f] [Separated f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    CohomologicalSpectralSequenceNat.ConvergesTo (alternatingCechSpectralSequence f F)
      (fun k ↦ (Sheaf.functorH (smallEtaleTopology X) k).obj F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
