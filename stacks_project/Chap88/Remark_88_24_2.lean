/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigEtale.Characterization
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale.Diagonal
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion.RigSmoothRigSurjective
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective.Diagonal
import StacksCheckRecall

/-!
# Comparison with Artin's definition of a formal modification

For a proper morphism of locally Noetherian formal algebraic spaces,
Remark 88.24.2 compares Artin II Definition 1.7 with the Stacks conditions of
Definition 88.24.1: containment of an ideal of definition in each of the Cramer
and Jacobian ideals versus algebraic `RigEtale`,
rig-étaleness of the relative diagonal, the étale-affine kernel test versus
`RigSurjective (pullback.diagonal f)`, and lifting every adic complete-DVR test
map over the original ring versus `RigSurjective f` once the diagonal is
rig-étale and rig-surjective. The canonical results below apply more generally
without the common properness hypothesis.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

/- Artin's condition that the Cramer and Jacobian ideals of
a morphism each contain an ideal of definition agrees with algebraic
`RigEtale I B`, because Lemma 88.8.2 (7) equates `P.fittingContainsPow` with
`RigEtale I B`: these are entries 6 and 0 of the seven-way equivalence. -/
#check (Algebra.RigEtale.tfae :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [Algebra.TopologicallyFiniteType I B] {ι : Type u} [Fintype ι]
    (P : Algebra.NaiveCotangent.Adic.Presentation A B I ι),
    List.TFAE
      [Algebra.RigEtale I B,
        ∃ c : ℕ, P.powSmulIdEqZero c,
        ∃ c : ℕ, P.homologyAnnihilated c,
        ∃ c : ℕ, P.stageHomologyAnnihilated c,
        P.existsRelationGenerators,
        P.existsElementarySquare,
        P.fittingContainsPow])

/- Remark 88.24.2: if `f` is rig-étale, then the relative diagonal
`pullback.diagonal f : X ⟶ pullback f f` is rig-étale as a morphism of locally
Noetherian formal algebraic spaces which are rig-étale over `X` (via `𝟙 X`
and `pr_1 = pullback.fst f f`). See Lemmas 88.20.5 and 88.20.7, using
`pullback.diagonal f ≫ pullback.fst f f = 𝟙 X`. -/
@[stacks 0GDL]
#check (AlgebraicGeometry.FormalAlgebraicSpace.RigEtale.diagonal :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [RigEtale f],
    RigEtale (pullback.diagonal f))

/- For the rig-étale diagonal established above, specialize the following
closed-immersion criterion to `pullback.diagonal f`. Since its rig-étaleness
is already known, Artin's condition that its ideal is annihilated by an ideal of
definition of `pullback f f` agrees with `RigSurjective (diagonal f)`, by the
étale-affine kernel test `etaleAffine_kernelKilled` of Lemma 88.21.13. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion.rigEtale_and_rigSurjective_iff_kernel :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [ClosedImmersion f],
    RigEtale f ∧ RigSurjective f ↔ ClosedImmersion.etaleAffine_kernelKilled f)

/- Artin's third condition: Artin's on-the-nose lifting of adic morphisms
`Spf(R) ⟶ Y` from a complete discrete valuation ring `R` does not match
`RigSurjective` (which allows a DVR extension), but once `diagonal f` is
rig-étale and rig-surjective the two agree by Lemma 88.22.3. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective.iff_adicSpf_lifts :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [RigEtale (pullback.diagonal f)]
    [RigSurjective (pullback.diagonal f)],
    RigSurjective f ↔
      ∀ sq : AdicSpfSquare f, ∃ lift : sq.specSpf ⟶ X, lift ≫ f = sq.p)
