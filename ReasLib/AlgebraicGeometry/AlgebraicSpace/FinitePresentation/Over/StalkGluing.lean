/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePresentation.Over.BaseChange

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

/-- If `s` is a closed point of a scheme and its open complement has
quasi-compact inclusion, canonical base change gives an equivalence between
finite-presentation algebraic spaces over the scheme and the categorical
pullback of those over the complement and the local spectrum over their
intersection. -/
theorem stalkGlueFunctor_isEquivalence (U : S.Opens)
    [AlgebraicGeometry.QuasiCompact U.ι] (s : S) (hs : s ∈ closedPoints S)
    (hU : (U : Set S) = ({s} : Set S)ᶜ) :
    (stalkGlueFunctor U s).IsEquivalence :=
  sorry

/-- The stalk-gluing comparison is an equivalence when closedness of the point
and identification of the open complement are supplied by `Fact` instances. -/
instance stalkGlueFunctor_isEquivalence_of_fact (U : S.Opens)
    [AlgebraicGeometry.QuasiCompact U.ι] (s : S) [Fact (s ∈ closedPoints S)]
    [Fact ((U : Set S) = ({s} : Set S)ᶜ)] :
    (stalkGlueFunctor U s).IsEquivalence :=
  stalkGlueFunctor_isEquivalence U s Fact.out Fact.out

end AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver
