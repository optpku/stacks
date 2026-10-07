module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.Fibered.InSetoids.Basic
public import stacks_project.Chap99.Lemma_99_11_7_Pushforward
public import stacks_project.Chap99.Lemma_99_11_7_WithSection

/-!
# Lemma 99.11.7

In Situation 99.11.1, if `σ : B ⟶ X` is a section and
`O_T ⟶ f_{T,*} O_{X_T}` is an isomorphism for every scheme `T` over `B`,
then Picardstack_{X/B, σ} ⟶ (Sch/S) is fibred in setoids, with isomorphism
classes over `T` the coproduct over `h : T ⟶ B` of `Ker(σ_T^*)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Picard

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 99.11.7 (1): in Situation 99.11.1, if `σ : B ⟶ X` is a section of
`f : X ⟶ B` and `O_T ⟶ f_{T,*} O_{X_T}` is an isomorphism for every scheme
`T` over `B`, then the projection Picardstack_{X/B, σ} ⟶ (Sch/S)_fppf is
fibred in setoids. -/
@[stacks 0D2B]
instance instIsFiberedInSetoids (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    [IsIsoBaseChangeStructurePushforward f] :
    Functor.IsFibered.InSetoids (WithSection.p f σ hσ) :=
  sorry

namespace WithSection

/-- Lemma 99.11.7 (2): in Situation 99.11.1, under the same hypotheses, the
isomorphism classes of Picardstack_{X/B, σ} over `T` are the coproduct over
`h : T ⟶ B` of `Ker(σ_T^* : Pic(X ×_{B,h} T) → Pic(T))`. -/
@[stacks 0D2B]
def isoClassEquiv (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    [IsIsoBaseChangeStructurePushforward f] (T : Over S) :
    isomorphismClasses.obj (Cat.of ((p f σ hσ).Fiber T)) ≃ IsoClass f σ hσ T where
  toFun :=
    Quotient.lift isoClassOfFiber fun x y h ↦ isoClassOfFiber_eq_of_isIsomorphic h
  invFun c := Quotient.mk _ (fiberOfIsoClass c)
  left_inv := sorry
  right_inv := sorry

/-- Evaluation of `isoClassEquiv` on the class of a fibre object. -/
theorem isoClassEquiv_apply (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    [IsIsoBaseChangeStructurePushforward f] {T : Over S}
    (x : (p f σ hσ).Fiber T) :
    isoClassEquiv f σ hσ T (Quotient.mk _ x) = isoClassOfFiber x :=
  sorry

/-- The inverse of `isoClassEquiv` reconstructs the class of `fiberOfIsoClass`. -/
theorem isoClassEquiv_symm_apply (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    [IsIsoBaseChangeStructurePushforward f] {T : Over S}
    (c : IsoClass f σ hσ T) :
    (isoClassEquiv f σ hσ T).symm c = Quotient.mk _ (fiberOfIsoClass c) :=
  sorry

end WithSection

end AlgebraicGeometry.AlgebraicSpace.Picard
