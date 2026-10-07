module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.JacobsonSpace
public import stacks_project.Chap70.Lemma_70_18_4_StalkGlue

/-!
# Glueing algebraic spaces of finite presentation near finitely many closed points

If `s : ι → S` is a finite family of pairwise distinct closed points and
`U = S \ range s → S` is quasi-compact, base change gives an equivalence from
algebraic spaces of finite presentation over `S` to the 2-fibre product of those
over `U` and over the product of the stalk schemes `S i = Spec(𝒪_{S, s i})`
above the product of the complementary opens `U i`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver

/-- Lemma 70.18.4: let `S` be a scheme. Let `s : ι → S` be finitely many pairwise
distinct closed points such that `U = S \ range s → S` is quasi-compact. With
`S i = Spec(𝒪_{S, s i})` and `U i = S i \ {s i}` there is an equivalence of
categories
`FP_S ⥤ FP_U ×_{(∀ i, FP_{U i})} (∀ i, FP_{S i})`, where `FP_T` is the category
of algebraic spaces of finite presentation over `T`. The functor is
`stalkGlueFamilyFunctor U s`, using the identified model
`U i = (S.fromSpecStalk (s i)) ⁻¹ᵁ U`. -/
@[stacks 0E92]
theorem stalkGlueFamilyFunctor_isEquivalence {ι : Type} [Finite ι] {S : Scheme.{u}}
    (U : S.Opens) [AlgebraicGeometry.QuasiCompact U.ι] (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S) (hs_inj : Function.Injective s)
    (hU : (U : Set S) = (Set.range s)ᶜ) :
    (stalkGlueFamilyFunctor U s).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver
