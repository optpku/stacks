module

public import stacks_project.Chap59.Lemma_59_104_1_EtaleSheafDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleSheaf

/-- Lemma 59.104.2: if `f : X ⟶ Y` is a surjective integral morphism of schemes,
then the functor from Type-valued sheaves on `Y.smallEtaleTopology` to singleton
descent data along `{X → Y}`, sending a sheaf to its canonical descent datum, is an
equivalence of categories. -/
@[stacks 0GEZ]
theorem descentIsEquivalenceOfSurjectiveIntegral {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Surjective f] [IsIntegralHom f] :
    (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f)).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.EtaleSheaf
