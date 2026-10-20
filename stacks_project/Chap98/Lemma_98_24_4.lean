module

public import stacks_project.Chap98.Lemma_98_24_3_NaiveCotangent
public import stacks_project.Chap98.Definition_98_13_1_Versal
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.AlgebraicGeometry.GroupoidsOver.DualObstruction.VersalAt
import StacksCheckRecall

/-!
# Neighbourhood spreading of versality for dual obstruction data

In Situation 98.24.2, connecting-compatibility of obstruction classes together
with perfectness of `K` in `D(A)` spreads versality at a closed finite-type
point of `U = Spec(A)` to every finite type point of some open neighbourhood.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor TopologicalSpace
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : GroupoidsOver S} [HasStrongRimSchlessinger X]

namespace DualObstruction

/- Lemma 98.24.4. In Situation 98.24.2, assume that (iv) of Lemma 98.24.3
holds and that `K` is a perfect object of `D(A)`. If `x` is versal at a
closed point `u0 ∈ U`, then there exists an open neighbourhood
`u0 ∈ U' ⊂ U` such that `x` is versal at every finite type point of `U'`. -/
@[stacks 07YZ]
#check (AlgebraicGeometry.GroupoidsOver.DualObstruction.exists_isVersalAt_nhd_of_closed :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] (𝒟 : DualObstruction X)
    (h_connecting : IsConnectingCompatible 𝒟)
    (h_perfect : DerivedCategory.IsPerfect 𝒟.derivedObject)
    (u0 : Spec (CommRingCat.of 𝒟.carrier)) [IsFiniteTypePoint u0]
    [𝒟.IsVersalAt u0] (h_closed : IsClosed {u0}),
    ∃ U' : Opens (Spec (CommRingCat.of 𝒟.carrier)),
      u0 ∈ U' ∧
        ∀ u, u ∈ U' → IsFiniteTypePoint u →
          𝒟.IsVersalAt u)

end DualObstruction

end AlgebraicGeometry.GroupoidsOver
