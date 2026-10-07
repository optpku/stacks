module

public import stacks_project.Chap75.Definition_75_3_2_SupportedOn
public import stacks_project.Chap75.Definition_75_9_1_Square
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Lemma 75.14.3: let `S` be a scheme and let `(U ⊂ X, f : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. If `E` is a perfect object of
`D(𝒪_V)` supported on `f⁻¹(T)` with `T = |X| \ |U|`, then `Rf_* E` is a perfect
object of `D(𝒪_X)`. The source morphism `j : V → X` is this étale map `f`, the
complement `T` is `(toOpenSubspace j f).pointsSetᶜ`, and `Rj_* E` is
`(pushforwardDerived f).obj E`. -/
@[stacks 08HK]
theorem IsPerfect.pushforwardDerived_of_isSupportedOn
    {S : Scheme.{u}} {U V X : AlgebraicSpace S} (j : U ⟶ X) (f : V ⟶ X)
    [IsElementaryDistinguishedSquare j f] {E : ModuleDerived V} (hE : IsPerfect E)
    (h_support : IsSupportedOn E (Points.map f ⁻¹' (toOpenSubspace j f).pointsSetᶜ)) :
    IsPerfect ((Modules.pushforwardDerived f).obj E) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
