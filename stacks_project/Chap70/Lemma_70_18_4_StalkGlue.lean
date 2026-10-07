module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.CategoryTheory.Pi.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import stacks_project.Chap70.Lemma_70_18_1_BaseChange
public import stacks_project.Chap70.Lemma_70_18_1_FinitePresentationOver

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

/-- If every `s i` is a closed point and `U = S \ range s`, then the
open `(S.fromSpecStalk (s i)) ⁻¹ᵁ U` is the identified model of the source open
`U i = S i \ {s i}`. -/
theorem preimage_eq_puncturedOpen (U : S.Opens) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hU : (U : Set S) = (Set.range s)ᶜ) (i : ι) :
    ((S.fromSpecStalk (s i)) ⁻¹ᵁ U : Set (Spec (S.presheaf.stalk (s i)))) =
      {IsLocalRing.closedPoint (S.presheaf.stalk (s i))}ᶜ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver
