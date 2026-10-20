/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Pi.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePresentation.Over.StalkGluing
public import ReasLib.AlgebraicGeometry.Scheme.Topology.Stalk

/-!
# Finite-presentation glueing near a family of closed points

The Pi-assembled cospan of finite-presentation base-change functors associated
to an open `U ⊆ S` and a family of stalk maps `S.fromSpecStalk (s i)`, together
with the comparison functor into the corresponding 2-fibre product.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoricalPullback
open scoped CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver

variable {ι : Type} {S : Scheme.{u}}

/-- The product of base-change functors `FP_U ⥤ ∀ i, FP_{U i}`, where
`U i = (S.fromSpecStalk (s i)) ⁻¹ᵁ U`. -/
def baseChangeToStalkOpens (U : S.Opens) (s : ι → S) :
    FinitePresentationOver U ⥤
      ∀ i, FinitePresentationOver ((S.fromSpecStalk (s i)) ⁻¹ᵁ U) :=
  Functor.pi' fun i ↦ baseChange (S.fromSpecStalk (s i) ∣_ U)

/-- The product of base-change functors
`(∀ i, FP_{S i}) ⥤ ∀ i, FP_{U i}`, where `S i = Spec(𝒪_{S, s i})` and
`U i = (S.fromSpecStalk (s i)) ⁻¹ᵁ U`. -/
def baseChangeStalkFamilyToOpens (U : S.Opens) (s : ι → S) :
    (∀ i, FinitePresentationOver (Spec (S.presheaf.stalk (s i)))) ⥤
      ∀ i, FinitePresentationOver ((S.fromSpecStalk (s i)) ⁻¹ᵁ U) :=
  Functor.pi fun i ↦ baseChange ((S.fromSpecStalk (s i)) ⁻¹ᵁ U).ι

/-- The product of base-change functors `FP_S ⥤ ∀ i, FP_{S i}`, where
`S i = Spec(𝒪_{S, s i})`. -/
def baseChangeToStalkFamily (s : ι → S) :
    FinitePresentationOver S ⥤
      ∀ i, FinitePresentationOver (Spec (S.presheaf.stalk (s i))) :=
  Functor.pi' fun i ↦ baseChange (S.fromSpecStalk (s i))

/-- The commutative square of finite-presentation base-change functors associated
to an open `U ⊆ S` and the family of stalk maps `S.fromSpecStalk (s i)`. -/
def stalkGlueFamilySquare (U : S.Opens) (s : ι → S) :
    CatCommSqOver (baseChangeToStalkOpens U s) (baseChangeStalkFamilyToOpens U s)
      (FinitePresentationOver S) where
  fst := baseChange U.ι
  snd := baseChangeToStalkFamily s
  iso :=
    NatIso.pi' fun i ↦
      (compIso (S.fromSpecStalk (s i) ∣_ U) U.ι).symm ≪≫
        eqToIso
          (congrArg
            (fun g : ((S.fromSpecStalk (s i)) ⁻¹ᵁ U).toScheme ⟶ S ↦ baseChange g)
            (morphismRestrict_ι (S.fromSpecStalk (s i)) U)) ≪≫
        compIso ((S.fromSpecStalk (s i)) ⁻¹ᵁ U).ι (S.fromSpecStalk (s i))

/-- The functor
`FP_S ⥤ FP_U ×_{(∀ i, FP_{U i})} (∀ i, FP_{S i})` given by base change, where
`S i = Spec(𝒪_{S, s i})` and `U i = (S.fromSpecStalk (s i)) ⁻¹ᵁ U`. -/
def stalkGlueFamilyFunctor (U : S.Opens) (s : ι → S) :
    FinitePresentationOver S ⥤
      (baseChangeToStalkOpens U s) ⊡ (baseChangeStalkFamilyToOpens U s) :=
  (stalkGlueFamilySquare U s).comparison

/-- Projecting the family stalk-glue comparison to the first factor recovers
base change along `U.ι`. -/
def stalkGlueFamilyFunctor_fst (U : S.Opens) (s : ι → S) :
    stalkGlueFamilyFunctor U s ⋙
        π₁ (baseChangeToStalkOpens U s) (baseChangeStalkFamilyToOpens U s) ≅
      baseChange U.ι :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- Projecting the family stalk-glue comparison to the second factor recovers
base change along the family of stalk maps. -/
def stalkGlueFamilyFunctor_snd (U : S.Opens) (s : ι → S) :
    stalkGlueFamilyFunctor U s ⋙
        π₂ (baseChangeToStalkOpens U s) (baseChangeStalkFamilyToOpens U s) ≅
      baseChangeToStalkFamily s :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- For a finite family of pairwise distinct closed points whose open complement
has quasi-compact inclusion, canonical base change is an equivalence from
finite-presentation algebraic spaces over the scheme to the categorical pullback
of those over the complement and the family of local spectra over their
pulled-back opens. -/
theorem stalkGlueFamilyFunctor_isEquivalence {ι : Type} [Finite ι] {S : Scheme.{u}}
    (U : S.Opens) [AlgebraicGeometry.QuasiCompact U.ι] (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S) (hs_inj : Function.Injective s)
    (hU : (U : Set S) = (Set.range s)ᶜ) :
    (stalkGlueFamilyFunctor U s).IsEquivalence :=
  sorry

/-- The finite-family stalk-gluing comparison is an equivalence when closedness,
injectivity, and identification of the open complement are supplied by `Fact` instances. -/
instance stalkGlueFamilyFunctor_isEquivalence_of_fact [Finite ι] (U : S.Opens)
    [AlgebraicGeometry.QuasiCompact U.ι] (s : ι → S)
    [Fact (∀ i, s i ∈ closedPoints S)] [Fact (Function.Injective s)]
    [Fact ((U : Set S) = (Set.range s)ᶜ)] :
    (stalkGlueFamilyFunctor U s).IsEquivalence :=
  stalkGlueFamilyFunctor_isEquivalence U s Fact.out Fact.out Fact.out

end AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver
