module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Lemma_88_8_2
public import stacks_project.Chap88.Lemma_88_21_13
public import stacks_project.Chap88.Lemma_88_22_3
import StacksCheckRecall

/-!
# Comparison with Artin's definition of a formal modification

Remark 88.24.2 compares Artin II Definition 1.7 with the Stacks conditions of
Definition 88.24.1: Fitting containment versus algebraic `RigEtale`,
rig-étaleness of the relative diagonal, the étale-affine kernel test versus
`RigSurjective (diagonal f)`, and on-the-nose complete-DVR lifting versus
`RigSurjective f` once the diagonal is rig-étale and rig-surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace Algebra.RigEtale

/-- Remark 88.24.2 (1): Artin's condition that the Cramer and Jacobian ideals of
a morphism each contain an ideal of definition agrees with algebraic
`RigEtale I B`, because Lemma 88.8.2 (7) equates `P.fittingContainsPow` with
`RigEtale I B`. -/
@[stacks 0GDL]
theorem iff_fittingContainsPow {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [TopologicallyFiniteType I B] {ι : Type u} [Fintype ι]
    (P : NaiveCotangent.Adic.Presentation A B I ι) :
    P.fittingContainsPow ↔ RigEtale I B :=
  sorry

end Algebra.RigEtale

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Remark 88.24.2 (2): if `f` is rig-étale and adic, then the relative diagonal
`diagonal f : X ⟶ pullback f f` is rig-étale as a morphism of locally
Noetherian formal algebraic spaces which are rig-étale over `X` (via `𝟙 X`
and `pr_1 = pullback.fst f f`). See Lemmas 88.20.5 and 88.20.7, using
`diagonal f ≫ pullback.fst f f = 𝟙 X`. -/
@[stacks 0GDL]
theorem RigEtale.diagonal {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [HasPullback f f] [IsFormalAlgebraicSpace (pullback f f)]
    [IsLocallyNoetherian (pullback f f)] [RigEtale f]
    (hf : AlgebraicSpace.representableByAlgebraicSpaces f) :
    RigEtale (diagonal f) :=
  sorry

/-- Remark 88.24.2 (3): if `diagonal f` is a rig-étale closed immersion, then
Artin's condition that the ideal of `diagonal f` is annihilated by an ideal of
definition of `pullback f f` agrees with `RigSurjective (diagonal f)`, by the
étale-affine kernel test `etaleAffine_kernelKilled` of Lemma 88.21.13. -/
@[stacks 0GDL]
theorem ClosedImmersion.rigSurjective_diagonal_iff_kernel
    {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [HasPullback f f] [IsFormalAlgebraicSpace (pullback f f)]
    [IsLocallyNoetherian (pullback f f)] [ClosedImmersion (diagonal f)]
    [LocallyOfFiniteType (diagonal f)] [RigEtale (diagonal f)] :
    ClosedImmersion.etaleAffine_kernelKilled (diagonal f) ↔
      RigSurjective (diagonal f) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace

/- Remark 88.24.2 (4): Artin's on-the-nose lifting of adic morphisms
`Spf(R) ⟶ Y` from a complete discrete valuation ring `R` does not match
`RigSurjective` (which allows a DVR extension), but once `diagonal f` is
rig-étale and rig-surjective the two agree by Lemma 88.22.3. -/
@[stacks 0GDL]
#check RigSurjective.iff_adicSpf_lifts
