/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import stacks_project.Chap70.Lemma_70_18_1_BaseChange
public import stacks_project.Chap70.Lemma_70_18_1_FinitePresentationOver

/-!
# Glueing algebraic spaces of finite presentation near a closed point

If `s ∈ S` is a closed point and `U = S \ {s} → S` is quasi-compact, base change
gives an equivalence from algebraic spaces of finite presentation over `S` to the
2-fibre product of those over `U` and over `Spec(𝒪_{S,s})` above those over
`V = Spec(𝒪_{S,s}) \ {s}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoricalPullback
open scoped CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver

variable {S : Scheme.{u}}

/-- The commutative square of finite-presentation base-change functors associated
to an open `U ⊆ S` and the stalk map `S.fromSpecStalk s`. -/
def stalkGlueSquare (U : S.Opens) (s : S) :
    CatCommSqOver
      (baseChange ((S.fromSpecStalk s) ∣_ U))
      (baseChange ((S.fromSpecStalk s) ⁻¹ᵁ U).ι)
      (FinitePresentationOver S) where
  fst := baseChange U.ι
  snd := baseChange (S.fromSpecStalk s)
  iso :=
    (compIso ((S.fromSpecStalk s) ∣_ U) U.ι).symm ≪≫
      eqToIso
        (congrArg
          (fun g : ((S.fromSpecStalk s) ⁻¹ᵁ U).toScheme ⟶ S ↦ baseChange g)
          (morphismRestrict_ι (S.fromSpecStalk s) U)) ≪≫
      compIso ((S.fromSpecStalk s) ⁻¹ᵁ U).ι (S.fromSpecStalk s)

/-- The functor `FP_S ⥤ FP_U ×_{FP_V} FP_{Spec(𝒪_{S,s})}` given by base change,
where `V = (S.fromSpecStalk s) ⁻¹ᵁ U`. -/
def stalkGlueFunctor (U : S.Opens) (s : S) :
    FinitePresentationOver S ⥤
      (baseChange ((S.fromSpecStalk s) ∣_ U)) ⊡
        (baseChange ((S.fromSpecStalk s) ⁻¹ᵁ U).ι) :=
  (stalkGlueSquare U s).comparison

/-- Projecting the stalk-glue comparison to the first factor recovers base change
along `U.ι`. -/
def stalkGlueFunctor_fst (U : S.Opens) (s : S) :
    stalkGlueFunctor U s ⋙
        π₁ (baseChange ((S.fromSpecStalk s) ∣_ U))
          (baseChange ((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≅
      baseChange U.ι :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- Projecting the stalk-glue comparison to the second factor recovers base change
along `S.fromSpecStalk s`. -/
def stalkGlueFunctor_snd (U : S.Opens) (s : S) :
    stalkGlueFunctor U s ⋙
        π₂ (baseChange ((S.fromSpecStalk s) ∣_ U))
          (baseChange ((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≅
      baseChange (S.fromSpecStalk s) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- Lemma 70.18.2: let `S` be a scheme. Let `s ∈ S` be a closed point such that
`U = S \ {s} → S` is quasi-compact. With `V = Spec(𝒪_{S,s}) \ {s}` there is an
equivalence of categories `FP_S ⥤ FP_U ×_{FP_V} FP_{Spec(𝒪_{S,s})}`, where
`FP_T` is the category of algebraic spaces of finite presentation over `T`.
Here `V` is `(S.fromSpecStalk s) ⁻¹ᵁ U` when `U = S \ {s}`, and the functor is
`stalkGlueFunctor U s`. -/
@[stacks 0E90]
theorem stalkGlueFunctor_isEquivalence (U : S.Opens)
    [AlgebraicGeometry.QuasiCompact U.ι] (s : S) (hs : s ∈ closedPoints S)
    (hU : (U : Set S) = ({s} : Set S)ᶜ) :
    (stalkGlueFunctor U s).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver
