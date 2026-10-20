module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Groupoid
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeSquare
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Diagonal.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.DottedArrow

/-!
# Valuative squares of the relative diagonal

A valuative 2-square of `Hom.diagonal f` unpacks to an associated valuative
square of `f` together with two dotted arrows `(a₁, α₁, id)` and
`(a₂, α₂, φ)`. Isomorphism classes of dotted arrows of the original square
are identified with morphisms between those two dotted arrows.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory Pseudofunctor.StrongTrans

noncomputable section

universe u

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace AlgebraicGeometry.AlgebraicStack.ValuativeCommSq

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]
variable {f : X ⟶ Y}
variable (sq : ValuativeCommSq (Hom.diagonal.{u + 1, u, u + 1} f))

/-- The first projection `a₁` of the bottom map `sq.i₂ : Spec(R) ⟶ X ×_Y X`. -/
def fstArrow : GroupoidsOver.slice sq.specR ⟶ X :=
  sq.i₂ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f

/-- The second projection `a₂` of the bottom map `sq.i₂ : Spec(R) ⟶ X ×_Y X`. -/
def sndArrow : GroupoidsOver.slice sq.specR ⟶ X :=
  sq.i₂ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f

/-- The comparison `2`-isomorphism `φ : a₁ ≫ f ≅ a₂ ≫ f` of the bottom map. -/
def comparison : fstArrow sq ≫ f ≅ sndArrow sq ≫ f :=
  α_ sq.i₂ (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f) f ≪≫
    whiskerLeftIso sq.i₂ (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} f f) ≪≫
    (α_ sq.i₂ (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f) f).symm

/-- The left triangular comparison `α₁ : j ≫ a₁ ≅ x` extracted from `γ`. -/
def leftIso : sq.verticalMap ≫ fstArrow sq ≅ sq.i₁ :=
  (α_ sq.verticalMap sq.i₂ (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f)).symm ≪≫
    whiskerRightIso sq.iso (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f) ≪≫
    α_ sq.i₁ (Hom.diagonal.{u + 1, u, u + 1} f)
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f) ≪≫
    whiskerLeftIso sq.i₁ (Hom.diagonal.fstIso.{u + 1, u, u + 1} f) ≪≫
    ρ_ sq.i₁

/-- The right triangular comparison `α₂ : j ≫ a₂ ≅ x` extracted from `γ`. -/
def rightIso : sq.verticalMap ≫ sndArrow sq ≅ sq.i₁ :=
  (α_ sq.verticalMap sq.i₂ (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f)).symm ≪≫
    whiskerRightIso sq.iso (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f) ≪≫
    α_ sq.i₁ (Hom.diagonal.{u + 1, u, u + 1} f)
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f) ≪≫
    whiskerLeftIso sq.i₁ (Hom.diagonal.sndIso.{u + 1, u, u + 1} f) ≪≫
    ρ_ sq.i₁

/-- The pair cone on `f, f` with legs `a₁`, `a₂` and comparison `φ`. -/
private def pairCone : PseudoPullbackCone f f where
  pt := GroupoidsOver.slice sq.specR
  fst := fstArrow sq
  snd := sndArrow sq
  iso := comparison sq

/-- The associated valuative square of `f` with bottom map `f ∘ a₁`. -/
def ofDiagonal : ValuativeCommSq f :=
  of sq.R sq.K sq.structureHom sq.i₁ (fstArrow sq ≫ f)
    ((α_ sq.verticalMap (fstArrow sq) f).symm ≪≫ whiskerRightIso (leftIso sq) f)

/-- The valuation ring of `ofDiagonal` is the original valuation ring. -/
@[simp]
theorem ofDiagonal_R : (ofDiagonal sq).R = sq.R :=
  rfl

/-- The fraction field of `ofDiagonal` is the original fraction field. -/
@[simp]
theorem ofDiagonal_K : (ofDiagonal sq).K = sq.K :=
  rfl

/-- The structure morphism of `ofDiagonal` is the original structure morphism. -/
@[simp]
theorem ofDiagonal_structureHom : (ofDiagonal sq).structureHom = sq.structureHom :=
  rfl

/-- The top map of `ofDiagonal` is the original top map `x`. -/
@[simp]
theorem ofDiagonal_i₁ : (ofDiagonal sq).i₁ = sq.i₁ :=
  rfl

/-- The bottom map of `ofDiagonal` is `f ∘ a₁`. -/
@[simp]
theorem ofDiagonal_i₂ : (ofDiagonal sq).i₂ = fstArrow sq ≫ f :=
  rfl

/-- The outer `2`-cell of `ofDiagonal` is obtained by whiskering `α₁` with `f`. -/
@[simp]
theorem ofDiagonal_iso :
    (ofDiagonal sq).iso =
      (α_ sq.verticalMap (fstArrow sq) f).symm ≪≫ whiskerRightIso (leftIso sq) f :=
  rfl

/-- The first projected triangular comparisons compose to the associated outer comparison. -/
private theorem fstDottedArrow_comm :
    whiskerLeftIso (ofDiagonal sq).toCone.fst (Iso.refl (fstArrow sq ≫ f)) ≪≫
        (α_ (ofDiagonal sq).toCone.fst (fstArrow sq) f).symm ≪≫
        whiskerRightIso (leftIso sq) f =
      (ofDiagonal sq).toCone.iso :=
  sorry

/-- The dotted arrow `(a₁, α₁, id)` of the associated valuative square of `f`. -/
def fstDottedArrow : DottedArrow (ofDiagonal sq).toCone where
  arrow := fstArrow sq
  left := leftIso sq
  right := Iso.refl (fstArrow sq ≫ f)
  comm := fstDottedArrow_comm sq

/-- The dotted morphism of `fstDottedArrow` is `a₁`. -/
@[simp]
theorem fstDottedArrow_arrow : (fstDottedArrow sq).arrow = fstArrow sq :=
  rfl

/-- The left comparison of `fstDottedArrow` is `α₁`. -/
@[simp]
theorem fstDottedArrow_left : (fstDottedArrow sq).left = leftIso sq :=
  rfl

/-- The right comparison of `fstDottedArrow` is the identity on `f ∘ a₁`. -/
@[simp]
theorem fstDottedArrow_right :
    (fstDottedArrow sq).right = Iso.refl (fstArrow sq ≫ f) :=
  rfl

/-- The second projected triangular comparisons compose to the associated outer comparison. -/
private theorem sndDottedArrow_comm :
    whiskerLeftIso (ofDiagonal sq).toCone.fst (comparison sq) ≪≫
        (α_ (ofDiagonal sq).toCone.fst (sndArrow sq) f).symm ≪≫
        whiskerRightIso (rightIso sq) f =
      (ofDiagonal sq).toCone.iso :=
  sorry

/-- The dotted arrow `(a₂, α₂, φ)` of the associated valuative square of `f`. -/
def sndDottedArrow : DottedArrow (ofDiagonal sq).toCone where
  arrow := sndArrow sq
  left := rightIso sq
  right := comparison sq
  comm := sndDottedArrow_comm sq

/-- The dotted morphism of `sndDottedArrow` is `a₂`. -/
@[simp]
theorem sndDottedArrow_arrow : (sndDottedArrow sq).arrow = sndArrow sq :=
  rfl

/-- The left comparison of `sndDottedArrow` is `α₂`. -/
@[simp]
theorem sndDottedArrow_left : (sndDottedArrow sq).left = rightIso sq :=
  rfl

/-- The right comparison of `sndDottedArrow` is `φ`. -/
@[simp]
theorem sndDottedArrow_right : (sndDottedArrow sq).right = comparison sq :=
  rfl

/-- First-projection comparison of a diagonal fill-in with `a₁`. -/
private def toHom_fstIso (A : DottedArrow sq.toCone) : fstArrow sq ≅ A.arrow :=
  whiskerRightIso A.right (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f) ≪≫
    α_ A.arrow (Hom.diagonal.{u + 1, u, u + 1} f)
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f) ≪≫
    whiskerLeftIso A.arrow (Hom.diagonal.fstIso.{u + 1, u, u + 1} f) ≪≫
    ρ_ A.arrow

/-- Second-projection comparison of a diagonal fill-in with `a₂`. -/
private def toHom_sndIso (A : DottedArrow sq.toCone) : sndArrow sq ≅ A.arrow :=
  whiskerRightIso A.right (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f) ≪≫
    α_ A.arrow (Hom.diagonal.{u + 1, u, u + 1} f)
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f) ≪≫
    whiskerLeftIso A.arrow (Hom.diagonal.sndIso.{u + 1, u, u + 1} f) ≪≫
    ρ_ A.arrow

/-- The projection comparison of a diagonal fill-in respects the upper-left triangles. -/
private theorem toHom_left_comm (A : DottedArrow sq.toCone) :
    (ofDiagonal sq).toCone.fst ◁
          ((toHom_fstIso sq A).hom ≫ (toHom_sndIso sq A).inv) ≫
        (sndDottedArrow sq).left.hom =
      (fstDottedArrow sq).left.hom :=
  sorry

/-- The projection comparison of a diagonal fill-in respects the lower-right triangles. -/
private theorem toHom_right_comm (A : DottedArrow sq.toCone) :
    (fstDottedArrow sq).right.hom ≫
        ((toHom_fstIso sq A).hom ≫ (toHom_sndIso sq A).inv) ▷ f =
      (sndDottedArrow sq).right.hom :=
  sorry

/-- The morphism `(a₁, α₁, id) ⟶ (a₂, α₂, φ)` associated to a diagonal fill-in. -/
def toHom (A : DottedArrow sq.toCone) :
    fstDottedArrow sq ⟶ sndDottedArrow sq where
  hom := (toHom_fstIso sq A).hom ≫ (toHom_sndIso sq A).inv
  left_comm := toHom_left_comm sq A
  right_comm := toHom_right_comm sq A

/-- First-projection comparison of `a₁ ≫ Hom.diagonal f` with `a₁`. -/
private def ofHom_fstIso :
    (fstArrow sq ≫ Hom.diagonal.{u + 1, u, u + 1} f) ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f ≅
      fstArrow sq :=
  α_ (fstArrow sq) (Hom.diagonal.{u + 1, u, u + 1} f)
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f) ≪≫
    whiskerLeftIso (fstArrow sq) (Hom.diagonal.fstIso.{u + 1, u, u + 1} f) ≪≫
    ρ_ (fstArrow sq)

/-- Second-projection comparison of `a₁ ≫ Hom.diagonal f` with `a₂`, via `θ`. -/
private def ofHom_sndIso (θ : fstDottedArrow sq ⟶ sndDottedArrow sq) :
    (fstArrow sq ≫ Hom.diagonal.{u + 1, u, u + 1} f) ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f ≅
      sndArrow sq :=
  α_ (fstArrow sq) (Hom.diagonal.{u + 1, u, u + 1} f)
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f) ≪≫
    whiskerLeftIso (fstArrow sq) (Hom.diagonal.sndIso.{u + 1, u, u + 1} f) ≪≫
    ρ_ (fstArrow sq) ≪≫ asIso θ.hom

/-- Vertexwise presentation of `sq.i₂` as `pairCone`. -/
private def i₂_app :
    ∀ j : LocallyDiscrete Limits.WalkingCospan,
      (((TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f).toPseudoCone.comparison
            (GroupoidsOver.slice sq.specR)).obj sq.i₂).app j ≅
        (pairCone sq).toPseudoCone.π.app j
  | ⟨Limits.WalkingCospan.one⟩ =>
    (α_ sq.i₂ (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f) f).symm
  | ⟨Limits.WalkingCospan.left⟩ => Iso.refl _
  | ⟨Limits.WalkingCospan.right⟩ => Iso.refl _

/-- Walking-cospan naturality of `i₂_app`. -/
private theorem i₂_naturality :
    ∀ {a b : LocallyDiscrete Limits.WalkingCospan} (h : a ⟶ b),
      (Pseudofunctor.const (LocallyDiscrete Limits.WalkingCospan)
            (GroupoidsOver.slice sq.specR)).map h ◁
          (i₂_app sq b).hom ≫
        ((pairCone sq).toPseudoCone.π.naturality h).hom =
      ((((TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f).toPseudoCone.comparison
              (GroupoidsOver.slice sq.specR)).obj sq.i₂).naturality h).hom ≫
        (i₂_app sq a).hom ▷ (Bicategory.cospan f f).map h :=
  sorry

/-- Invertible modification presenting `sq.i₂` as `pairCone`. -/
private def i₂_presentation :
    ((TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f).toPseudoCone.comparison
          (GroupoidsOver.slice sq.specR)).obj sq.i₂ ≅
      (pairCone sq).toPseudoCone.π :=
  Pseudofunctor.StrongTrans.isoMk (i₂_app sq) (i₂_naturality sq)

/-- `sq.i₂` is the universal lift of `pairCone`. -/
private def i₂_unique :
    sq.i₂ ≅
      PseudoPullbackCone.lift (pairCone sq)
        (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f) :=
  PseudoPullbackCone.lift.uniqueIso (pairCone sq)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f) sq.i₂ (i₂_presentation sq)

/-- Vertexwise presentation of `a₁ ≫ Hom.diagonal f` as `pairCone`, using `θ`. -/
private def ofHom_app (θ : fstDottedArrow sq ⟶ sndDottedArrow sq) :
    ∀ j : LocallyDiscrete Limits.WalkingCospan,
      (((TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f).toPseudoCone.comparison
            (GroupoidsOver.slice sq.specR)).obj
          (fstArrow sq ≫ Hom.diagonal.{u + 1, u, u + 1} f)).app j ≅
        (pairCone sq).toPseudoCone.π.app j
  | ⟨Limits.WalkingCospan.one⟩ =>
    (α_ (fstArrow sq ≫ Hom.diagonal.{u + 1, u, u + 1} f)
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f) f).symm ≪≫
      whiskerRightIso (ofHom_fstIso sq) f
  | ⟨Limits.WalkingCospan.left⟩ => ofHom_fstIso sq
  | ⟨Limits.WalkingCospan.right⟩ => ofHom_sndIso sq θ

/-- Walking-cospan naturality of `ofHom_app`. -/
private theorem ofHom_naturality (θ : fstDottedArrow sq ⟶ sndDottedArrow sq) :
    ∀ {a b : LocallyDiscrete Limits.WalkingCospan} (h : a ⟶ b),
      (Pseudofunctor.const (LocallyDiscrete Limits.WalkingCospan)
            (GroupoidsOver.slice sq.specR)).map h ◁
          (ofHom_app sq θ b).hom ≫
        ((pairCone sq).toPseudoCone.π.naturality h).hom =
      ((((TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f).toPseudoCone.comparison
              (GroupoidsOver.slice sq.specR)).obj
            (fstArrow sq ≫ Hom.diagonal.{u + 1, u, u + 1} f)).naturality h).hom ≫
        (ofHom_app sq θ a).hom ▷ (Bicategory.cospan f f).map h :=
  sorry

/-- Invertible modification presenting `a₁ ≫ Hom.diagonal f` as `pairCone`. -/
private def ofHom_presentation (θ : fstDottedArrow sq ⟶ sndDottedArrow sq) :
    ((TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f).toPseudoCone.comparison
          (GroupoidsOver.slice sq.specR)).obj
        (fstArrow sq ≫ Hom.diagonal.{u + 1, u, u + 1} f) ≅
      (pairCone sq).toPseudoCone.π :=
  Pseudofunctor.StrongTrans.isoMk (ofHom_app sq θ) (ofHom_naturality sq θ)

/-- `a₁ ≫ Hom.diagonal f` is the universal lift of `pairCone` once `θ` identifies `a₂` with `a₁`. -/
private def ofHom_unique (θ : fstDottedArrow sq ⟶ sndDottedArrow sq) :
    fstArrow sq ≫ Hom.diagonal.{u + 1, u, u + 1} f ≅
      PseudoPullbackCone.lift (pairCone sq)
        (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f) :=
  PseudoPullbackCone.lift.uniqueIso (pairCone sq)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f)
    (fstArrow sq ≫ Hom.diagonal.{u + 1, u, u + 1} f) (ofHom_presentation sq θ)

/-- The unique `2`-isomorphism `sq.i₂ ≅ a₁ ≫ Hom.diagonal f` determined by `θ`. -/
private def ofHom_right (θ : fstDottedArrow sq ⟶ sndDottedArrow sq) :
    sq.i₂ ≅ fstArrow sq ≫ Hom.diagonal.{u + 1, u, u + 1} f :=
  i₂_unique sq ≪≫ (ofHom_unique sq θ).symm

/-- The reconstructed triangular comparisons compose to the original outer comparison. -/
private theorem ofHom_comm (θ : fstDottedArrow sq ⟶ sndDottedArrow sq) :
    whiskerLeftIso sq.toCone.fst (ofHom_right sq θ) ≪≫
        (α_ sq.toCone.fst (fstArrow sq) (Hom.diagonal.{u + 1, u, u + 1} f)).symm ≪≫
        whiskerRightIso (leftIso sq) (Hom.diagonal.{u + 1, u, u + 1} f) =
      sq.toCone.iso :=
  sorry

/-- The diagonal fill-in associated to a morphism `(a₁, α₁, id) ⟶ (a₂, α₂, φ)`. -/
def ofHom (θ : fstDottedArrow sq ⟶ sndDottedArrow sq) : DottedArrow sq.toCone where
  arrow := fstArrow sq
  left := leftIso sq
  right := ofHom_right sq θ
  comm := ofHom_comm sq θ

/-- The dotted-arrow category of a valuative square of the relative diagonal is thin. -/
private theorem diagonalDottedArrowThin : Quiver.IsThin (DottedArrow sq.toCone) :=
  dottedArrow_isThin_of_diagonal_separated
    (Groupoids.Hom.has_separated_diagonal
      (Groupoids.Hom.relativelyRepresentableByAlgebraicSpaces_diagonal f)) sq

/-- The dotted-arrow category of a valuative square of `Hom.diagonal f` is a setoid. -/
instance dottedArrow_isThin : Quiver.IsThin (DottedArrow sq.toCone) :=
  diagonalDottedArrowThin sq

/-- Isomorphic diagonal fill-ins induce the same compatible morphism. -/
private theorem toHom_respects_iso (A B : DottedArrow sq.toCone)
    (h : Nonempty (A ≅ B)) : toHom sq A = toHom sq B :=
  sorry

/-- Reconstructing a diagonal fill-in from `toHom` recovers an isomorphic fill-in. -/
theorem ofHom_toHom (A : DottedArrow sq.toCone) :
    Nonempty (ofHom sq (toHom sq A) ≅ A) :=
  sorry

/-- The morphism associated to `ofHom θ` is `θ`. -/
theorem toHom_ofHom (θ : fstDottedArrow sq ⟶ sndDottedArrow sq) :
    toHom sq (ofHom sq θ) = θ :=
  sorry


/-- Isomorphism classes of diagonal fill-ins are morphisms `(a₁, α₁, id) ⟶ (a₂, α₂, φ)`. -/
def isoClassEquiv :
    isomorphismClasses.obj (Cat.of (DottedArrow sq.toCone)) ≃
      (fstDottedArrow sq ⟶ sndDottedArrow sq) where
  toFun := Quotient.lift (fun A ↦ toHom sq A) (toHom_respects_iso sq)
  invFun := fun θ ↦ Quotient.mk'' (ofHom sq θ)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro A
    exact Quotient.sound (ofHom_toHom sq A)
  right_inv := toHom_ofHom sq

/-- The forward map of `isoClassEquiv` sends the class of a fill-in to `toHom`. -/
theorem isoClassEquiv_mk (A : DottedArrow sq.toCone) :
    isoClassEquiv sq (Quotient.mk'' A) = toHom sq A :=
  rfl

/-- The inverse map of `isoClassEquiv` sends a morphism of base dotted arrows to the class of `ofHom`. -/
theorem isoClassEquiv_symm_apply (θ : fstDottedArrow sq ⟶ sndDottedArrow sq) :
    (isoClassEquiv sq).symm θ = Quotient.mk'' (ofHom sq θ) :=
  rfl


end AlgebraicGeometry.AlgebraicStack.ValuativeCommSq
