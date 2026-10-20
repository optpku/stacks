/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Pullbacks and coproducts of algebraic spaces

The pullback of a small coproduct is canonically isomorphic to the coproduct of the pullbacks.
-/

-- Public constructions retain their explicit bodies while their implementation facts stay private.
set_option backward.privateInPublic true

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace.ReasLibPullback

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

variable {I : Type v} [Small.{u} I] {S : Scheme.{u}}

/-- Fibre products of a map `Z ⟶ P` with each summand of a family mapping to `P`. -/
abbrev pullbackSummands {P Z : AlgebraicSpace S} {G : I → AlgebraicSpace S}
    (h : ∀ i, G i ⟶ P) (g : Z ⟶ P) : I → AlgebraicSpace S :=
  fun i ↦ pullbackOver (h i) g P.isSheaf P.representableDiagonal

/-- The coproduct-inclusion triangle for a fibre product with a summand. -/
private theorem pullbackSummand_fac {P Z : AlgebraicSpace S} {G : I → AlgebraicSpace S}
    (h : ∀ i, G i ⟶ P) (g : Z ⟶ P) (i : I) :
    pullbackOverFst (h i) g P.isSheaf P.representableDiagonal ≫ coproductι G i ≫ coproductDesc h =
      pullbackOverSnd (h i) g P.isSheaf P.representableDiagonal ≫ g := sorry

/-- The comparison from the coproduct of fibre products with the summands to the fibre product
with the coproduct. -/
noncomputable def pullbackCoproductHom {P Z : AlgebraicSpace S} {G : I → AlgebraicSpace S}
    (h : ∀ i, G i ⟶ P) (g : Z ⟶ P) :
    coproduct (pullbackSummands h g) ⟶
      pullbackOver (coproductDesc h) g P.isSheaf P.representableDiagonal :=
  coproductDesc fun i ↦
    pullbackLift (coproductDesc h) g
      (pullbackOverFst (h i) g P.isSheaf P.representableDiagonal ≫ coproductι G i)
      (pullbackOverSnd (h i) g P.isSheaf P.representableDiagonal)
      (pullbackSummand_fac h g i)

/-- Sections with equal images in the base have compatible restrictions on every clopen piece. -/
private theorem pullbackCoproductInvSummand_compat {P Z : AlgebraicSpace S}
    {G : I → AlgebraicSpace S} (h : ∀ i, G i ⟶ P) (g : Z ⟶ P)
    {T : Over S} (v : CoproductSection G T) (z : Z.functorOfPoints.obj (op T))
    (compatible : yonedaEquiv.symm v ≫ coproductDesc h = yonedaEquiv.symm z ≫ g)
    (i : Shrink.{u} I) :
    yonedaEquiv.symm (v.summandSection i) ≫ h ((equivShrink.{u} I).symm i) =
      yonedaEquiv.symm
          (Z.functorOfPoints.map (Over.homMk (v.piece i).ι).op z) ≫ g := sorry

/-- The summand section of the coproduct-of-pullbacks comparison over a clopen piece. -/
private noncomputable def pullbackCoproductInvSummand {P Z : AlgebraicSpace S}
    {G : I → AlgebraicSpace S} (h : ∀ i, G i ⟶ P) (g : Z ⟶ P)
    {T : Over S} (v : CoproductSection G T) (z : Z.functorOfPoints.obj (op T))
    (compatible : yonedaEquiv.symm v ≫ coproductDesc h = yonedaEquiv.symm z ≫ g)
    (i : Shrink.{u} I) :
    (pullbackOver (h ((equivShrink.{u} I).symm i)) g
        P.isSheaf P.representableDiagonal).functorOfPoints.obj
      (op (Over.mk ((v.piece i).ι ≫ T.hom))) :=
  yonedaEquiv
    (pullback.lift
      (yonedaEquiv.symm (v.summandSection i))
      (yonedaEquiv.symm (Z.functorOfPoints.map (Over.homMk (v.piece i).ι).op z))
      (pullbackCoproductInvSummand_compat h g v z compatible i))

/-- The coproduct-of-pullbacks section associated to a section of a fibre product with a
coproduct. -/
private noncomputable def pullbackCoproductInvSection {P Z : AlgebraicSpace S}
    {G : I → AlgebraicSpace S} (h : ∀ i, G i ⟶ P) (g : Z ⟶ P)
    (T : (Over S)ᵒᵖ)
    (s : (pullbackOver (coproductDesc h) g
        P.isSheaf P.representableDiagonal).functorOfPoints.obj T) :
    CoproductSection (pullbackSummands h g) (unop T) where
  piece :=
    (pullbackOverFst (coproductDesc h) g P.isSheaf P.representableDiagonal |>.app T s).piece
  isClopen :=
    (pullbackOverFst (coproductDesc h) g P.isSheaf P.representableDiagonal |>.app T s).isClopen
  pairwiseDisjoint :=
    (pullbackOverFst (coproductDesc h) g P.isSheaf P.representableDiagonal |>.app T s).pairwiseDisjoint
  iSup_eq_top :=
    (pullbackOverFst (coproductDesc h) g P.isSheaf P.representableDiagonal |>.app T s).iSup_eq_top
  summandSection :=
    pullbackCoproductInvSummand h g
      (pullbackOverFst (coproductDesc h) g P.isSheaf P.representableDiagonal |>.app T s)
      (pullbackOverSnd (coproductDesc h) g P.isSheaf P.representableDiagonal |>.app T s)
      (by
        rw [← yonedaEquiv_symm_naturality_right,
          ← yonedaEquiv_symm_naturality_right, Category.assoc, Category.assoc]
        exact congrArg (fun t ↦ yonedaEquiv.symm s ≫ t)
          (ReasLibPullback.isPullback (coproductDesc h) g).w)

/-- The comparison from a fibre product with a coproduct to the coproduct of the fibre products
with the summands. -/
noncomputable def pullbackCoproductInv {P Z : AlgebraicSpace S} {G : I → AlgebraicSpace S}
    (h : ∀ i, G i ⟶ P) (g : Z ⟶ P) :
    pullbackOver (coproductDesc h) g P.isSheaf P.representableDiagonal ⟶
      coproduct (pullbackSummands h g) where
  app T := ↾fun s ↦ pullbackCoproductInvSection h g T s
  naturality := sorry

/-- The forward pullback–coproduct comparison restricts to the canonical lift on each summand. -/
theorem pullbackCoproductHom_ι {P Z : AlgebraicSpace S} {G : I → AlgebraicSpace S}
    (h : ∀ i, G i ⟶ P) (g : Z ⟶ P) (i : I) :
    coproductι (pullbackSummands h g) i ≫ pullbackCoproductHom h g =
      pullbackLift (coproductDesc h) g
        (pullbackOverFst (h i) g P.isSheaf P.representableDiagonal ≫ coproductι G i)
        (pullbackOverSnd (h i) g P.isSheaf P.representableDiagonal)
        (pullbackSummand_fac h g i) := sorry

/-- The forward pullback–coproduct comparison followed by its inverse is the identity. -/
theorem pullbackCoproduct_hom_inv_id {P Z : AlgebraicSpace S} {G : I → AlgebraicSpace S}
    (h : ∀ i, G i ⟶ P) (g : Z ⟶ P) :
    pullbackCoproductHom h g ≫ pullbackCoproductInv h g =
      𝟙 (coproduct (pullbackSummands h g)) := sorry

/-- The inverse pullback–coproduct comparison followed by the forward map is the identity. -/
theorem pullbackCoproduct_inv_hom_id {P Z : AlgebraicSpace S} {G : I → AlgebraicSpace S}
    (h : ∀ i, G i ⟶ P) (g : Z ⟶ P) :
    pullbackCoproductInv h g ≫ pullbackCoproductHom h g =
      𝟙 (pullbackOver (coproductDesc h) g P.isSheaf P.representableDiagonal) := sorry

/-- Pullback commutes with small coproducts of algebraic spaces. -/
noncomputable def pullbackCoproductIso {P Z : AlgebraicSpace S} {G : I → AlgebraicSpace S}
    (h : ∀ i, G i ⟶ P) (g : Z ⟶ P) :
    coproduct (pullbackSummands h g) ≅
      pullbackOver (coproductDesc h) g P.isSheaf P.representableDiagonal where
  hom := pullbackCoproductHom h g
  inv := pullbackCoproductInv h g
  hom_inv_id := pullbackCoproduct_hom_inv_id h g
  inv_hom_id := pullbackCoproduct_inv_hom_id h g

end AlgebraicGeometry.AlgebraicSpace
