module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper.OpennessOfVersality
public import ReasLib.AlgebraicGeometry.GroupoidsOver.DualObstruction.VersalAt
public import ReasLib.AlgebraicGeometry.GroupoidsOver.ObstructionTheory.OpennessOfVersality

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces TopologicalSpace
open AlgebraicGeometry.GroupoidsOver

universe u

/- Remark 99.13.10 (1): Lemma 99.13.9, that `Spaces'_{fp, flat, proper}` satisfies
openness of versality over `specZ` and, after Remark 99.13.5, over any
Noetherian base `S`, can also be shown by the two Artin routes below. In both
cases one uses the deformation and obstruction theory of Cotangent Section
92.23 to translate the needed properties into Ext-groups to which Lemma
75.23.3 applies. The obstruction-theory route, using the full cotangent
complex, is the standard method. -/
@[stacks 0D1P] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.opennessOfVersality :
    ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {U : Scheme.{u}}
    (hU : U ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType hU] (x : FpFlatProperGroupoids S)
    (hx : (pFpFlatProperGroupoids S).obj x = Over.mk hU) (u0 : U),
    IsFiniteTypePoint u0 → FpFlatProperGroupoids.IsVersalAt hU x hx u0 →
      ∃ U' : Opens U, u0 ∈ U' ∧
        ∀ u : U, u ∈ U' → IsFiniteTypePoint u → FpFlatProperGroupoids.IsVersalAt hU x hx u)

/- Remark 99.13.10 (2): the first alternative is Artin's Axioms Lemma 98.24.4
(dual obstruction), as in the first proof of Lemma 99.5.11. -/
@[stacks 0D1P] #check (AlgebraicGeometry.GroupoidsOver.DualObstruction.exists_isVersalAt_nhd_of_closed :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] (𝒟 : DualObstruction X)
    (h_connecting : DualObstruction.IsConnectingCompatible 𝒟)
    (h_perfect : DerivedCategory.IsPerfect 𝒟.derivedObject)
    (u0 : Spec (CommRingCat.of 𝒟.carrier)) [IsFiniteTypePoint u0]
    [𝒟.IsVersalAt u0] (h_closed : IsClosed {u0}),
    ∃ U' : Opens (Spec (CommRingCat.of 𝒟.carrier)),
      u0 ∈ U' ∧
        ∀ u, u ∈ U' → IsFiniteTypePoint u →
          𝒟.IsVersalAt u)

/- Remark 99.13.10 (3): the second, standard alternative is an obstruction
theory as in Artin's Axioms Lemma 98.22.2, as in the second proof of Lemma
99.5.11. -/
@[stacks 0D1P] #check (AlgebraicGeometry.GroupoidsOver.OpennessOfVersality.ofObstructionTheory :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] [Groupoids.LimitPreserving X]
    (h_diag : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    (𝒪 : ObstructionTheory X) (hT : tangentFunctor.preservesNatPi X)
    (hO : 𝒪.natPiComparison_injective),
    OpennessOfVersality X)
