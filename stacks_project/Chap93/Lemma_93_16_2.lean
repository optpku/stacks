module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap93.Lemma_93_16_2_Pair

/-!
# Smoothness of glueing maps of scheme deformation categories

In Situation 93.9.9, smoothness of `U₁₂ ⟶ Spec(k)` implies smoothness of
`Def_X ⥤ᵇ Def_{U₁} ×_{C_Λ} Def_{U₂}`. If in addition `U₁` is a local complete
intersection over `k`, restriction `Def_X ⥤ᵇ Def_{U₂}` is smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped AlgebraicGeometry BasedFunctor

universe u

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {X : Scheme.{u}} (c : TwoAffineOpenCover X)
variable (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
variable [AlgebraicGeometry.Flat hX]

/-- Lemma 93.16.2 (1)
In Situation 93.9.9, if `U₁₂ ⟶ Spec(k)` is smooth, then the morphism
`toOpenProduct : Def_X ⥤ᵇ openProduct` of categories cofibered in groupoids
over `ArtinianLocalAlgCat` is smooth. -/
@[stacks 0DZN]
instance instIsSmooth_toOpenProduct [Smooth (structureHomInf Λ k c hX)] :
    BasedFunctor.IsSmooth (toOpenProduct Λ k c hX) :=
  sorry

/-- Lemma 93.16.2 (2)
In Situation 93.9.9, if `U₁₂ ⟶ Spec(k)` is smooth and `U₁` is a local complete
intersection over `k`, then `restrictOpen` to `U₂` is a smooth morphism of
categories cofibered in groupoids over `ArtinianLocalAlgCat`. -/
@[stacks 0DZN]
instance instIsSmooth_restrictOpen_U₂ [Smooth (structureHomInf Λ k c hX)]
    [Syntomic (structureHom₁ Λ k c hX)] :
    BasedFunctor.IsSmooth (FlatSchemeCat.restrictOpen Λ k X hX c.U₂) :=
  sorry

/-- Infinitesimal lifting along surjections in `C_Λ` for `toOpenProduct` when
`U₁₂` is smooth over `k`. -/
theorem toOpenProduct_exists_lift [Smooth (structureHomInf Λ k c hX)]
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) (hf : Function.Surjective f.hom)
    {y : (openProduct Λ k c hX).obj} {x : (deformationBased Λ k hX).obj}
    (α : y ⟶ (toOpenProduct Λ k c hX).obj x)
    (hα : (openProduct Λ k c hX).p.IsHomLift f α) :
    ∃ (x' : (deformationBased Λ k hX).obj) (β : x' ⟶ x)
      (γ : (toOpenProduct Λ k c hX).obj x' ⟶ y),
      (deformationBased Λ k hX).p.IsHomLift f β ∧
        (openProduct Λ k c hX).p.IsHomLift (𝟙 B) γ ∧
        γ ≫ α = (toOpenProduct Λ k c hX).map β :=
  sorry

/-- Infinitesimal lifting along surjections in `C_Λ` for restriction to `U₂`
when `U₁₂` is smooth over `k` and `U₁` is a local complete intersection over `k`. -/
theorem restrictOpen_U₂_exists_lift [Smooth (structureHomInf Λ k c hX)]
    [Syntomic (structureHom₁ Λ k c hX)]
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) (hf : Function.Surjective f.hom)
    {y : (deformationBased_U₂ Λ k c hX).obj} {x : (deformationBased Λ k hX).obj}
    (α : y ⟶ (FlatSchemeCat.restrictOpen Λ k X hX c.U₂).obj x)
    (hα : (deformationBased_U₂ Λ k c hX).p.IsHomLift f α) :
    ∃ (x' : (deformationBased Λ k hX).obj) (β : x' ⟶ x)
      (γ : (FlatSchemeCat.restrictOpen Λ k X hX c.U₂).obj x' ⟶ y),
      (deformationBased Λ k hX).p.IsHomLift f β ∧
        (deformationBased_U₂ Λ k c hX).p.IsHomLift (𝟙 B) γ ∧
        γ ≫ α = (FlatSchemeCat.restrictOpen Λ k X hX c.U₂).map β :=
  sorry

end AlgebraicGeometry.Scheme.TwoAffineOpenCover
