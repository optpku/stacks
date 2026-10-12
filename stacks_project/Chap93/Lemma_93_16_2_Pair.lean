/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pair
public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap93.Lemma_93_9_6_Restrict
public import stacks_project.Chap93.Situation_93_9_9_Deformation

/-!
# Pairing of open restrictions of scheme deformations

The product `Def_{U₁} ×_{C_Λ} Def_{U₂}` of the deformation categories of the
two affine opens, and the pairing of the two restriction functors from `Def_X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped AlgebraicGeometry BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {X : Scheme.{u}} (c : TwoAffineOpenCover X)
variable (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
variable [AlgebraicGeometry.Flat hX]

/-- The based category `Def_X` over `ArtinianLocalAlgCat`. -/
abbrev deformationBased :=
  BasedCategory.ofFunctor
    (Over.forget (Fiber.fiberInclusion.obj (FlatSchemeCat.residueObj Λ k X hX)) ⋙
      FlatSchemeCat.forget Λ k)

/-- The based category `Def_{U₁}` over `ArtinianLocalAlgCat`. -/
abbrev deformationBased_U₁ :=
  BasedCategory.ofFunctor
    (Over.forget (Fiber.fiberInclusion.obj
        (FlatSchemeCat.residueObj Λ k c.U₁.toScheme (structureHom₁ Λ k c hX))) ⋙
      FlatSchemeCat.forget Λ k)

/-- The based category `Def_{U₂}` over `ArtinianLocalAlgCat`. -/
abbrev deformationBased_U₂ :=
  BasedCategory.ofFunctor
    (Over.forget (Fiber.fiberInclusion.obj
        (FlatSchemeCat.residueObj Λ k c.U₂.toScheme (structureHom₂ Λ k c hX))) ⋙
      FlatSchemeCat.forget Λ k)

/-- The product `Def_{U₁} ×_{C_Λ} Def_{U₂}` of deformation categories over
`ArtinianLocalAlgCat`. -/
abbrev openProduct :=
  BasedCategory.PseudoPullback
    (BasedCategory.toBase (deformationBased_U₁ Λ k c hX))
    (BasedCategory.toBase (deformationBased_U₂ Λ k c hX))

/-- The projection of `openProduct` evaluates to the stored Artinian base. -/
theorem openProduct_p_obj (P : (openProduct Λ k c hX).obj) :
    (openProduct Λ k c hX).p.obj P = BasedCategory.PseudoPullback.baseObj P :=
  sorry

/-- The pairing `Def_X ⥤ᵇ Def_{U₁} ×_{C_Λ} Def_{U₂}` of the two open restriction
functors. -/
def toOpenProduct : deformationBased Λ k hX ⥤ᵇ openProduct Λ k c hX :=
  BasedCategory.PseudoPullback.pair
    (FlatSchemeCat.restrictOpen Λ k X hX c.U₁)
    (FlatSchemeCat.restrictOpen Λ k X hX c.U₂)

/-- The underlying ordinary functor of `toOpenProduct` is the pairing of the two
open restrictions. -/
theorem toOpenProduct_toFunctor :
    (toOpenProduct Λ k c hX).toFunctor =
      (BasedCategory.PseudoPullback.pair
        (FlatSchemeCat.restrictOpen Λ k X hX c.U₁)
        (FlatSchemeCat.restrictOpen Λ k X hX c.U₂)).toFunctor :=
  sorry

/-- The first projection of `toOpenProduct` recovers restriction to `U₁`. -/
theorem toOpenProduct_fst :
    toOpenProduct Λ k c hX ⋙
      BasedCategory.PseudoPullback.fst
        (BasedCategory.toBase (deformationBased_U₁ Λ k c hX))
        (BasedCategory.toBase (deformationBased_U₂ Λ k c hX)) =
      FlatSchemeCat.restrictOpen Λ k X hX c.U₁ :=
  sorry

/-- The second projection of `toOpenProduct` recovers restriction to `U₂`. -/
theorem toOpenProduct_snd :
    toOpenProduct Λ k c hX ⋙
      BasedCategory.PseudoPullback.snd
        (BasedCategory.toBase (deformationBased_U₁ Λ k c hX))
        (BasedCategory.toBase (deformationBased_U₂ Λ k c hX)) =
      FlatSchemeCat.restrictOpen Λ k X hX c.U₂ :=
  sorry

/-- The slice projection of `Def_X` is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_deformationBased_op :
    Functor.IsFibered.InGroupoids (deformationBased Λ k hX).p.op :=
  sorry

/-- The slice projection of `Def_{U₁}` is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_deformationBased_U₁_op :
    Functor.IsFibered.InGroupoids (deformationBased_U₁ Λ k c hX).p.op :=
  sorry

/-- The slice projection of `Def_{U₂}` is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_deformationBased_U₂_op :
    Functor.IsFibered.InGroupoids (deformationBased_U₂ Λ k c hX).p.op :=
  sorry

/-- The product `Def_{U₁} ×_{C_Λ} Def_{U₂}` is cofibered in groupoids over
`ArtinianLocalAlgCat`. -/
instance instIsFiberedInGroupoids_openProduct_op :
    Functor.IsFibered.InGroupoids (openProduct Λ k c hX).p.op :=
  sorry

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end
