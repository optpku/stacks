/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Polarized.OpennessOfVersality
public import ReasLib.AlgebraicGeometry.GroupoidsOver.ObstructionTheory.OpennessOfVersality
public import ReasLib.AlgebraicGeometry.Polarized.Algebraic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper.OpennessOfVersality

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Polarized
open AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids
open AlgebraicGeometry.GroupoidsOver
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces

universe u

/- Remark 99.14.14 (1): Lemma 99.14.13, that Polarized satisfies openness of
versality over `specZ` and, after Remark 99.14.5, over any Noetherian base `S`,
can also be shown by the two routes below. The `specZ` specialization is
`instOpennessOfVersality`. -/
@[stacks 0D4W] #check
  (AlgebraicGeometry.Polarized.instOpennessOfVersality_over :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian S],
      AlgebraicGeometry.GroupoidsOver.OpennessOfVersality
        (AlgebraicGeometry.Polarized.toGroupoidsOver S))

#check
  (AlgebraicGeometry.Polarized.instOpennessOfVersality.{u} :
    AlgebraicGeometry.GroupoidsOver.OpennessOfVersality
      AlgebraicGeometry.Polarized.toGroupoidsOverSpecZ.{u})

/- Remark 99.14.14 (2): the first alternative is an obstruction theory as in
Artin's Axioms Lemma 98.22.2, as in the second proof of Lemma 99.5.11. To do
this one has to generalize the deformation and obstruction theory of Cotangent
Section 92.23 from ringed topoi to pairs of algebraic spaces and quasi-coherent
modules. -/
@[stacks 0D4W] #check (AlgebraicGeometry.GroupoidsOver.OpennessOfVersality.ofObstructionTheory :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] [Groupoids.LimitPreserving X]
    (h_diag : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    (𝒪 : ObstructionTheory X) (hT : tangentFunctor.preservesNatPi X)
    (hO : 𝒪.natPiComparison_injective),
    OpennessOfVersality X)

/- Remark 99.14.14 (3): the second alternative uses that the forgetful
1-morphism `toFpFlatProper : Polarized ⟶ Spaces'_{fp, flat, proper}` is
algebraic (Lemma 99.14.6). -/
@[stacks 0D4W] #check (AlgebraicGeometry.Polarized.instAlgebraicStack_twoFibreProduct :
  ∀ ξ : AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids
      (⊤_ AlgebraicGeometry.Scheme.{u}),
    AlgebraicGeometry.AlgebraicStack (AlgebraicGeometry.Polarized.twoFibreProduct ξ))

/- Remark 99.14.14 (4): openness of versality of the target
`Spaces'_{fp, flat, proper}` is already known by Lemma 99.13.9 and
Remark 99.13.10. -/
@[stacks 0D4W] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.opennessOfVersality :
  ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {U : Scheme.{u}}
    (hU : U ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType hU] (x : FpFlatProperGroupoids S)
    (hx : (pFpFlatProperGroupoids S).obj x = Over.mk hU) (u0 : U),
    IsFiniteTypePoint u0 →
      AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.IsVersalAt hU x hx u0 →
      ∃ U' : Opens U, u0 ∈ U' ∧
        ∀ u : U, u ∈ U' → IsFiniteTypePoint u →
          AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.IsVersalAt hU x hx u)
