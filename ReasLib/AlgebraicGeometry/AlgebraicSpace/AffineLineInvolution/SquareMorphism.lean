/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.AffineSpace.AdditiveGroup
public import ReasLib.AlgebraicGeometry.AffineSpace.SquareMap
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Representability
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

/-!
# The descended square morphism of the affine-line involution space

The morphism `X ⟶ 𝔸¹_k` induced by `x ↦ x²` on the atlas of the affine-line
involution space is an isomorphism away from `0`, has a unique field-valued point
over `0`, is universally injective, and is not separated in characteristic different from two.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

/-- The endomorphism of the affine-line atlas sending the coordinate to its square. -/
def squareOver (k : Type u) [Field k] : cover k ⟶ cover k :=
  Over.homMk (AffineSpace.squareMap k) (AffineSpace.squareMap_over k)

/-- The underlying scheme morphism of `squareOver` is the affine-line squaring map. -/
theorem squareOver_left (k : Type u) [Field k] :
    (squareOver k).left = AffineSpace.squareMap k := rfl

/-- Squaring equalizes the two projections of the involution relation, since
`x² = (-x)²`. -/
theorem squareOver_equalizes (k : Type u) [Field k] :
    (preRelation k).t ≫ squareOver k = (preRelation k).s ≫ squareOver k := by
  have hneg : involution k ≫ squareOver k = squareOver k := by
    apply Over.OverMorphism.ext
    change AffineSpace.negLeft (ULift.{u} (Fin 1)) (base k) ≫
      AffineSpace.squareMap k = AffineSpace.squareMap k
    apply AffineSpace.hom_ext
    · simp [AffineSpace.squareMap, AffineSpace.negLeft]
    · intro i
      simp [AffineSpace.squareMap, AffineSpace.negLeft]
  change (Sigma.desc (relationComponentHom k) ≫ prod.fst) ≫ squareOver k =
    (Sigma.desc (relationComponentHom k) ≫ prod.snd) ≫ squareOver k
  simp only [Category.assoc]
  apply Sigma.hom_ext
  intro i
  cases i
  · rw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc]
    change diagonalHom k ≫ prod.fst ≫ squareOver k =
      diagonalHom k ≫ prod.snd ≫ squareOver k
    rw [← Category.assoc, ← Category.assoc, diagonalHom,
      prod.lift_fst, prod.lift_snd]
  · rw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc]
    change graphHom k ≫ prod.fst ≫ squareOver k =
      graphHom k ≫ prod.snd ≫ squareOver k
    simp only [graphHom, Category.assoc, prod.lift_fst_assoc, prod.lift_snd_assoc,
      Category.id_comp, hneg]

/-- The origin `Spec k` of the affine line, viewed as a scheme over `Spec k`. -/
def originOver (k : Type u) [Field k] : Over (base k) :=
  Over.mk (AffineSpace.zeroLeft (ULift.{u} (Fin 1)) (base k) ≫ (cover k).hom)

/-- `originOver` is the zero section of the affine line, viewed in `Over (Spec k)`. -/
theorem originOver_eq (k : Type u) [Field k] :
    originOver k =
      Over.mk (AffineSpace.zeroLeft (ULift.{u} (Fin 1)) (base k) ≫ (cover k).hom) := rfl

/-- The origin morphism `Spec k ⟶ 𝔸¹_k` over `Spec k`. -/
def originToCover (k : Type u) [Field k] : originOver k ⟶ cover k :=
  Over.homMk (AffineSpace.zeroLeft (ULift.{u} (Fin 1)) (base k))

/-- The underlying scheme morphism of `originToCover` is the zero section of the affine line. -/
theorem originToCover_left (k : Type u) [Field k] :
    (originToCover k).left = AffineSpace.zeroLeft (ULift.{u} (Fin 1)) (base k) := rfl

/-- The descended morphism `X ⟶ 𝔸¹_k` induced by `x ↦ x²` on the atlas. -/
def toAffineLine (k : Type u) [Field k] :
    sheafOfPoints k ⟶
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (cover k) :=
  (preRelation k).quotientSheafDesc (Scheme.fppfTopology.over (base k))
    (squareOver k) (squareOver_equalizes k)

/-- `toAffineLine` is the canonical quotient-sheaf descent of `squareOver`. -/
theorem toAffineLine_eq (k : Type u) [Field k] :
    toAffineLine k =
      (preRelation k).quotientSheafDesc (Scheme.fppfTopology.over (base k))
        (squareOver k) (squareOver_equalizes k) := rfl

/-- On the atlas, `toAffineLine` recovers the squaring map `x ↦ x²`. -/
theorem toAffineLine_comp_atlas (k : Type u) [Field k] :
    atlas k ≫ toAffineLine k =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (squareOver k) := by
  let J := Scheme.fppfTopology.over (base k)
  let P := preRelation k
  apply J.uliftYonedaEquiv.injective
  rw [J.uliftYonedaEquiv_comp, J.uliftYonedaEquiv_uliftYoneda_map]
  have hatlas : J.uliftYonedaEquiv (atlas k) = P.quotientClass J (𝟙 (cover k)) :=
    J.uliftYonedaEquiv.apply_symm_apply _
  refine (congrArg ((toAffineLine k).hom.app (op (cover k))) hatlas).trans ?_
  have h := congrArg
    (fun f => f.app (op (cover k))
      (ULift.up (Quot.mk (P.pointRel (cover k)) (𝟙 (cover k)))))
    (toSheafify_sheafifyLift J
      (Functor.whiskerRight
        (P.quotientPresheafDesc (squareOver k) (squareOver_equalizes k))
        uliftFunctor.{u + 1, u})
      (J.uliftYoneda.{u + 1}.obj (cover k)).property)
  change (toAffineLine k).hom.app (op (cover k))
    (P.quotientClass J (𝟙 (cover k))) = ULift.up (𝟙 (cover k) ≫ squareOver k) at h
  exact h.trans (congrArg ULift.up (Category.id_comp (squareOver k)))

/-- `toAffineLine` is an isomorphism after base change along `D(x) ⟶ 𝔸¹_k`. -/
@[instance]
theorem isIso_over_punctured (k : Type u) [Field k] [NeZero (2 : k)] :
    IsIso
      (pullback.snd (toAffineLine k)
        ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (puncturedι k))) :=
  sorry

/-- The fibre over the origin has exactly one point over every field-valued object
over `Spec k`. -/
theorem unique_point_over_origin (k : Type u) [Field k] [NeZero (2 : k)]
    (K : Type u) [Field K] (σ : Spec (CommRingCat.of K) ⟶ base k) :
    Nonempty
        ((pullback (toAffineLine k)
            ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
              (originToCover k))).obj.obj
          (op (Over.mk σ))) ∧
      Subsingleton
        ((pullback (toAffineLine k)
            ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
              (originToCover k))).obj.obj
          (op (Over.mk σ))) :=
  sorry

/-- The relative diagonal of `toAffineLine` is a representable surjection, so the
morphism is universally injective. -/
theorem universallyInjective_toAffineLine (k : Type u) [Field k] [NeZero (2 : k)] :
    (MorphismProperty.over (@Surjective)).relative uliftYoneda.{u + 1}
      (pullback.diagonal (toAffineLine k)).hom := sorry

private theorem diagonal_mem_of_relative_diagonal_mem
    {C : Type*} [Category C] [HasPullbacks C] [HasBinaryProducts C] [HasTerminal C]
    {D : Type*} [Category D] (F : C ⥤ D)
    [PreservesLimitsOfShape WalkingCospan F]
    (P : MorphismProperty D) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [P.RespectsIso]
    {X Y : C} (f : X ⟶ Y)
    (hf : P (F.map (pullback.diagonal f))) (hY : P (F.map (diag Y))) :
    P (F.map (diag X)) := by
  let Q : MorphismProperty C := P.inverseImage F
  letI : Q.IsStableUnderBaseChange :=
    ⟨fun sq hg => P.of_isPullback (sq.map F) hg⟩
  have hdiag (T : C) : diag T =
      pullback.diagonal (terminal.from T) ≫ (prodIsoPullback T T).inv := by
    apply prod.hom_ext
    · simp only [Category.assoc, prodIsoPullback_inv_fst, pullback.diagonal_fst,
        prod.lift_fst]
    · simp only [Category.assoc, prodIsoPullback_inv_snd, pullback.diagonal_snd,
        prod.lift_snd]
  have hY' : Q.diagonal (terminal.from Y) := by
    change Q (pullback.diagonal (terminal.from Y))
    rw [← Q.cancel_right_of_respectsIso _ (prodIsoPullback Y Y).inv, ← hdiag]
    exact hY
  have hX := Q.diagonal.comp_mem f (terminal.from Y) hf hY'
  rw [terminal.comp_from] at hX
  change Q (diag X)
  rw [hdiag, Q.cancel_right_of_respectsIso]
  exact hX


/-- The relative diagonal of `toAffineLine` is not a closed immersion, so the
morphism is not separated. -/
theorem not_separated_toAffineLine (k : Type u) [Field k] [NeZero (2 : k)] :
    ¬ (MorphismProperty.over (@IsClosedImmersion)).relative uliftYoneda.{u + 1}
        (pullback.diagonal (toAffineLine k)).hom := by
  intro hf
  let J := Scheme.fppfTopology.over (base k)
  let F := sheafToPresheaf J (Type (u + 1))
  let G := J.uliftYoneda.{u + 1}
  haveI : PreservesLimitsOfShape (Discrete WalkingPair) F := by
    dsimp only [F]
    infer_instance
  haveI : PreservesLimitsOfShape (Discrete WalkingPair) G := by
    dsimp only [G]
    infer_instance
  let CClosed : MorphismProperty Scheme.{u} := @IsClosedImmersion
  let P₀ : MorphismProperty (Over (base k)) := MorphismProperty.over (@IsClosedImmersion)
  let P := P₀.relative uliftYoneda.{u + 1}
  letI : P₀.IsStableUnderBaseChange :=
    ⟨fun sq hg => CClosed.of_isPullback (sq.map (Over.forget (base k))) hg⟩
  letI : P₀.IsStableUnderComposition := by
    change (CClosed.inverseImage (Over.forget (base k))).IsStableUnderComposition
    infer_instance
  letI : P₀.RespectsIso := by
    change (CClosed.inverseImage (Over.forget (base k))).RespectsIso
    infer_instance
  letI : P.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange P₀
  have hcover : P₀ (diagonalHom k) := by
    change CClosed (diagonalHom k).left
    rw [← CClosed.cancel_right_of_respectsIso _
      (Over.prodLeftIsoPullback (cover k) (cover k)).hom]
    have hdiag : (diagonalHom k).left ≫
        (Over.prodLeftIsoPullback (cover k) (cover k)).hom =
          pullback.diagonal (cover k).hom := by
      apply pullback.hom_ext
      · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_fst,
          ← Over.comp_left, diagonalHom, prod.lift_fst, Over.id_left,
          pullback.diagonal_fst]
      · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_snd,
          ← Over.comp_left, diagonalHom, prod.lift_snd, Over.id_left,
          pullback.diagonal_snd]
    rw [hdiag]
    change IsClosedImmersion (pullback.diagonal (affineSpaceOverFieldHom k 1))
    infer_instance
  have hmap : P (F.map (G.map (diagonalHom k))) :=
    MorphismProperty.relative_map hcover
  have hG : G.map (diagonalHom k) ≫ prodComparison G (cover k) (cover k) =
      diag (G.obj (cover k)) := by
    apply prod.hom_ext
    · simp only [Category.assoc, prodComparison_fst, ← G.map_comp, diagonalHom,
        prod.lift_fst]
      exact G.map_id _
    · simp only [Category.assoc, prodComparison_snd, ← G.map_comp, diagonalHom,
        prod.lift_snd]
      exact G.map_id _
  have hY : P (F.map (diag (G.obj (cover k)))) := by
    rw [← hG, F.map_comp, P.cancel_right_of_respectsIso]
    exact hmap
  have hX := diagonal_mem_of_relative_diagonal_mem F P (toAffineLine k) hf hY
  have hF : F.map (diag (sheafOfPoints k)) ≫
      prodComparison F (sheafOfPoints k) (sheafOfPoints k) =
        diag (sheafOfPoints k).obj := by
    apply prod.hom_ext
    · simp only [Category.assoc, prodComparison_fst, ← F.map_comp,
        prod.lift_fst]
      exact (F.map_id _).trans (prod.lift_fst _ _).symm
    · simp only [Category.assoc, prodComparison_snd, ← F.map_comp,
        prod.lift_snd]
      exact (F.map_id _).trans (prod.lift_snd _ _).symm
  have hX' : P (diag (sheafOfPoints k).obj) := by
    haveI : IsIso (prodComparison F (sheafOfPoints k) (sheafOfPoints k)) := by
      dsimp only [F]
      infer_instance
    exact hF ▸ (P.cancel_right_of_respectsIso
      (F.map (diag (sheafOfPoints k)))
      (prodComparison F (sheafOfPoints k) (sheafOfPoints k))).mpr hX
  apply not_isImmersion_diag_sheafOfPoints k
  apply MorphismProperty.relative_monotone (P := P₀) (F := uliftYoneda.{u + 1}) ?_ _ hX'
  intro U V f hf
  haveI : IsClosedImmersion f.left := hf
  exact (inferInstance : IsImmersion f.left)

end AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution
