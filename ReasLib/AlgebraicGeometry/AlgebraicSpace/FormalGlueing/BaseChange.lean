/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing.Square
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Pullback

/-! # Base change of closed complements and formal-glueing squares -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormalGlueing

/-- The chosen fibre product `Z' = Z ×_X X'`, isomorphic to the symmetric fibre product
`X' ×_X Z` by `pullbackSymmetry`. -/
abbrev Z' {S : Scheme.{u}} {X Z X' : AlgebraicSpace S} (i : Z ⟶ X) (g : X' ⟶ X) :
    AlgebraicSpace S :=
  Limits.pullback i g

/-- The chosen fibre product `Y' = Y ×_X X'`, isomorphic to the symmetric fibre product
`X' ×_X Y` by `pullbackSymmetry`. -/
abbrev Y' {S : Scheme.{u}} {X Y X' : AlgebraicSpace S} (f : Y ⟶ X) (g : X' ⟶ X) :
    AlgebraicSpace S :=
  Limits.pullback f g

/-- The base change `i' : Z' ⟶ X'` of a closed immersion `i : Z ⟶ X`. -/
abbrev i' {S : Scheme.{u}} {X Z X' : AlgebraicSpace S} (i : Z ⟶ X) (g : X' ⟶ X) :
    Z' i g ⟶ X' :=
  Limits.pullback.snd i g

/-- The base change `f' : Y' ⟶ X'` of `f : Y ⟶ X`. -/
abbrev f' {S : Scheme.{u}} {X Y X' : AlgebraicSpace S} (f : Y ⟶ X) (g : X' ⟶ X) :
    Y' f g ⟶ X' :=
  Limits.pullback.snd f g

/-- The projection `Z' ⟶ Z` of the chosen fibre product. -/
abbrev toZ {S : Scheme.{u}} {X Z X' : AlgebraicSpace S} (i : Z ⟶ X) (g : X' ⟶ X) :
    Z' i g ⟶ Z :=
  Limits.pullback.fst i g

/-- The projection `Y' ⟶ Y` of the chosen fibre product. -/
abbrev toY {S : Scheme.{u}} {X Y X' : AlgebraicSpace S} (f : Y ⟶ X) (g : X' ⟶ X) :
    Y' f g ⟶ Y :=
  Limits.pullback.fst f g

/-- The base change `i' i g` of a closed immersion remains a closed immersion. -/
instance instIsClosedImmersion_i' {S : Scheme.{u}} {X Z X' : AlgebraicSpace S}
    (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    IsClosedImmersion (i' i g) :=
  IsClosedImmersion.of_isPullback (IsPullback.flip (IsPullback.of_hasPullback i g))

private theorem pointsImage_eq_preimage_of_isPullback {S : Scheme.{u}}
    {X Y Z P : AlgebraicSpace S} {f : Y ⟶ X} {i : Z ⟶ X}
    {pY : P ⟶ Y} {pZ : P ⟶ Z} (sq : IsPullback pY pZ f i) :
    pointsImage pY = Points.map f ⁻¹' pointsImage i := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨Points.map pZ p, ?_⟩
    simp only [← Points.map_comp, sq.w]
  · rintro ⟨z, hz⟩
    obtain ⟨p, hp, _⟩ := Points.exists_of_map_eq sq y z hz.symm
    exact ⟨p, hp⟩

private theorem missesClosedImage_iff_of_isPullback {S : Scheme.{u}}
    {X Y Z P : AlgebraicSpace S} {f : Y ⟶ X} {i : Z ⟶ X}
    {pY : P ⟶ Y} {pZ : P ⟶ Z} [IsClosedImmersion i] [IsClosedImmersion pY]
    (sq : IsPullback pY pZ f i) {W : (Over S)ᵒᵖ} (t : Y.functorOfPoints.obj W) :
    missesClosedImage pY t ↔ missesClosedImage i (f.app W t) := by
  have hcomp : homOfYonedaSection t ≫ f = homOfYonedaSection (f.app W t) :=
    yonedaEquiv_symm_naturality_right W.unop f t
  unfold missesClosedImage
  rw [pointsImage_eq_preimage_of_isPullback sq, ← hcomp]
  change (Set.range (Points.map (homOfYonedaSection t)) ⊆
      (Points.map f ⁻¹' pointsImage i)ᶜ) ↔
    (Set.range (Points.map (homOfYonedaSection t ≫ f)) ⊆ (pointsImage i)ᶜ)
  simp only [Set.range_subset_iff, Set.mem_compl_iff, Set.mem_preimage, Points.map_comp]

/-- The composite of the complement inclusion of `i' i g` with `g` misses the closed
image of `i`. -/
private theorem complementBaseChange_misses {S : Scheme.{u}} {X Z X' : AlgebraicSpace S}
    (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    ∀ (W : (Over S)ᵒᵖ)
      (t : (closedImmersionComplement (i' i g)).functorOfPoints.obj W),
      missesClosedImage i ((closedImmersionComplementι (i' i g) ≫ g).app W t) :=
  by
    intro W t
    exact (missesClosedImage_iff_of_isPullback
      (IsPullback.of_hasPullback i g).flip t.1).mp t.2

/-- The maps on complement sections commute with restriction of test objects. -/
private theorem complementBaseChange_naturality {S : Scheme.{u}} {X Z X' : AlgebraicSpace S}
    (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    {W W' : (Over S)ᵒᵖ} (h : W ⟶ W') :
    (closedImmersionComplement (i' i g)).functorOfPoints.map h ≫
        (TypeCat.ofHom fun t : (closedImmersionComplement (i' i g)).functorOfPoints.obj W' ↦
          (⟨(closedImmersionComplementι (i' i g) ≫ g).app W' t,
            complementBaseChange_misses i g W' t⟩ : (closedImmersionComplement i).functorOfPoints.obj W')) =
      (TypeCat.ofHom fun t : (closedImmersionComplement (i' i g)).functorOfPoints.obj W ↦
          (⟨(closedImmersionComplementι (i' i g) ≫ g).app W t,
            complementBaseChange_misses i g W t⟩ : (closedImmersionComplement i).functorOfPoints.obj W)) ≫ (closedImmersionComplement i).functorOfPoints.map h :=
  by
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    exact (closedImmersionComplementι (i' i g) ≫ g).naturality_apply h t

/-- The comparison `U' ⟶ U` of open complements of `i'` and `i`. -/
@[no_expose] def complementBaseChange {S : Scheme.{u}} {X Z X' : AlgebraicSpace S}
    (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    closedImmersionComplement (i' i g) ⟶ closedImmersionComplement i where
  app W := TypeCat.ofHom fun t ↦
    ⟨(closedImmersionComplementι (i' i g) ≫ g).app W t,
      complementBaseChange_misses i g W t⟩
  naturality _ _ h := complementBaseChange_naturality i g h

private theorem complementBaseChange_app_val {S : Scheme.{u}} {X Z X' : AlgebraicSpace S}
    (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] {W : (Over S)ᵒᵖ}
    (t : (closedImmersionComplement (i' i g)).functorOfPoints.obj W) :
    ((complementBaseChange i g).app W t).1 =
      (closedImmersionComplementι (i' i g) ≫ g).app W t :=
  rfl

/-- The square of complement inclusions over `g` commutes. -/
theorem complementBaseChange_comp {S : Scheme.{u}} {X Z X' : AlgebraicSpace S}
    (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    complementBaseChange i g ≫ closedImmersionComplementι i =
      closedImmersionComplementι (i' i g) ≫ g :=
  by
    apply NatTrans.ext
    funext W
    apply ConcreteCategory.hom_ext
    intro t
    exact complementBaseChange_app_val i g t

/-- The composite of the complement inclusion of `inverseImageι (f' f g) (i' i g)` with
`toY f g` misses the closed image of `inverseImageι f i`. -/
private theorem overlapBaseChange_misses {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    ∀ (W : (Over S)ᵒᵖ)
      (t : (closedImmersionComplement (inverseImageι (f' f g) (i' i g))).functorOfPoints.obj W),
      missesClosedImage (inverseImageι f i)
        ((closedImmersionComplementι (inverseImageι (f' f g) (i' i g)) ≫
            toY f g).app W t) :=
  by
    intro W t
    have h := (missesClosedImage_iff_of_isPullback
      (inverseImage_isPullback (f' f g) (i' i g)) t.1).mp t.2
    have h' := (missesClosedImage_iff_of_isPullback
      (IsPullback.of_hasPullback i g).flip ((f' f g).app W t.1)).mp h
    apply (missesClosedImage_iff_of_isPullback
      (inverseImage_isPullback f i) ((toY f g).app W t.1)).mpr
    change missesClosedImage i ((toY f g ≫ f).app W t.1)
    rw [pullback.condition (C := AlgebraicSpace S) (f := f) (g := g)]
    exact h'

/-- The maps on complement sections commute with restriction of test objects. -/
private theorem overlapBaseChange_naturality {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    {W W' : (Over S)ᵒᵖ} (h : W ⟶ W') :
    (closedImmersionComplement (inverseImageι (f' f g) (i' i g))).functorOfPoints.map h ≫
        (TypeCat.ofHom fun t : (closedImmersionComplement (inverseImageι (f' f g) (i' i g))).functorOfPoints.obj W' ↦
          (⟨(closedImmersionComplementι (inverseImageι (f' f g) (i' i g)) ≫ toY f g).app W' t,
            overlapBaseChange_misses f i g W' t⟩ : (closedImmersionComplement (inverseImageι f i)).functorOfPoints.obj W')) =
      (TypeCat.ofHom fun t : (closedImmersionComplement (inverseImageι (f' f g) (i' i g))).functorOfPoints.obj W ↦
          (⟨(closedImmersionComplementι (inverseImageι (f' f g) (i' i g)) ≫ toY f g).app W t,
            overlapBaseChange_misses f i g W t⟩ : (closedImmersionComplement (inverseImageι f i)).functorOfPoints.obj W)) ≫ (closedImmersionComplement (inverseImageι f i)).functorOfPoints.map h :=
  by
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    exact (closedImmersionComplementι (inverseImageι (f' f g) (i' i g)) ≫
      toY f g).naturality_apply h t

/-- The comparison `V' ⟶ V` of closed-immersion complements of the inverse images of
`i'` and `i`. -/
@[no_expose] def overlapBaseChange {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    closedImmersionComplement (inverseImageι (f' f g) (i' i g)) ⟶
      closedImmersionComplement (inverseImageι f i) where
  app W := TypeCat.ofHom fun t ↦
    ⟨(closedImmersionComplementι (inverseImageι (f' f g) (i' i g)) ≫ toY f g).app W t,
      overlapBaseChange_misses f i g W t⟩
  naturality _ _ h := overlapBaseChange_naturality f i g h

private theorem overlapBaseChange_app_val {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] {W : (Over S)ᵒᵖ}
    (t : (closedImmersionComplement (inverseImageι (f' f g) (i' i g))).functorOfPoints.obj W) :
    ((overlapBaseChange f i g).app W t).1 =
      (closedImmersionComplementι (inverseImageι (f' f g) (i' i g)) ≫ toY f g).app W t :=
  rfl

/-- The overlap of closed complements is compatible with restriction. -/
theorem overlapBaseChange_comp_restrict {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    overlapBaseChange f i g ≫ restrictToComplement f i =
      restrictToComplement (f' f g) (i' i g) ≫ complementBaseChange i g :=
  by
    apply NatTrans.ext
    funext W
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    change (closedImmersionComplementι i).app W
        ((restrictToComplement f i).app W ((overlapBaseChange f i g).app W t)) =
      ((complementBaseChange i g).app W
        ((restrictToComplement (f' f g) (i' i g)).app W t)).1
    rw [restrictToComplement_eq, complementBaseChange_app_val]
    change f.app W (((overlapBaseChange f i g).app W t).1) =
      g.app W ((closedImmersionComplementι (i' i g)).app W
        ((restrictToComplement (f' f g) (i' i g)).app W t))
    rw [overlapBaseChange_app_val, restrictToComplement_eq]
    exact congrArg (fun k ↦ k.app W t.1)
      (pullback.condition (C := AlgebraicSpace S) (f := f) (g := g))

/-- The overlap of closed complements is compatible with the inclusions into `Y'` and `Y`. -/
theorem overlapBaseChange_comp_ι {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    overlapBaseChange f i g ≫ closedImmersionComplementι (inverseImageι f i) =
      closedImmersionComplementι (inverseImageι (f' f g) (i' i g)) ≫ toY f g :=
  by
    apply NatTrans.ext
    funext W
    apply ConcreteCategory.hom_ext
    intro t
    exact overlapBaseChange_app_val f i g t

end AlgebraicGeometry.AlgebraicSpace.FormalGlueing

open AlgebraicGeometry.AlgebraicSpace.FormalGlueing

namespace AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing

/-- The comparison `V' ⟶ V` of open inverse images of the complements of `i'` and `i`. -/
@[no_expose] def overlapBaseChange {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    V (f' f g) (i' i g) ⟶ V f i :=
  pullback.map (C := (Over S)ᵒᵖ ⥤ Type u)
    (f' f g : (Y' f g).functorOfPoints ⟶ X'.functorOfPoints)
    (j (i' i g) : (U (i' i g)).functorOfPoints ⟶ X'.functorOfPoints)
    (f : Y.functorOfPoints ⟶ X.functorOfPoints)
    (j i : (U i).functorOfPoints ⟶ X.functorOfPoints)
    (toY f g) (complementBaseChange i g) g
    (pullback.condition (C := AlgebraicSpace S) (f := f) (g := g)).symm (complementBaseChange_comp i g).symm

private theorem overlapBaseChange_comp_restrictF_proof {S : Scheme.{u}}
    {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    overlapBaseChange f i g ≫ restrictF f i =
      restrictF (f' f g) (i' i g) ≫ complementBaseChange i g := by
  exact pullback.lift_snd (C := (Over S)ᵒᵖ ⥤ Type u)
    (f := (f : Y.functorOfPoints ⟶ X.functorOfPoints))
    (g := (j i : (U i).functorOfPoints ⟶ X.functorOfPoints)) _ _ _

/-- Open overlap is compatible with `restrictF`. -/
theorem overlapBaseChange_comp_restrictF {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    overlapBaseChange f i g ≫ restrictF f i =
      restrictF (f' f g) (i' i g) ≫
        complementBaseChange i g :=
  overlapBaseChange_comp_restrictF_proof f i g

private theorem overlapBaseChange_comp_j'_proof {S : Scheme.{u}}
    {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    overlapBaseChange f i g ≫ j' f i =
      j' (f' f g) (i' i g) ≫ toY f g := by
  exact pullback.lift_fst (C := (Over S)ᵒᵖ ⥤ Type u)
    (f := (f : Y.functorOfPoints ⟶ X.functorOfPoints))
    (g := (j i : (U i).functorOfPoints ⟶ X.functorOfPoints)) _ _ _

/-- Open overlap is compatible with the inclusions `j'`. -/
theorem overlapBaseChange_comp_j' {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    overlapBaseChange f i g ≫ j' f i =
      j' (f' f g) (i' i g) ≫
        toY f g :=
  overlapBaseChange_comp_j'_proof f i g

end AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing
