/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LeftLegDiagonal.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Projections
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Computations

/-!
# Presentations for left-leg diagonal squares

This leaf contains the explicit source/target cone presentations, their bilimit uniqueness
comparisons, and the resulting canonical comparison and square. The construction data itself is
defined in `Construction`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory.Bicategory.PseudoPullbackCone.LeftLegDiagonal

open Bicategory
open scoped Pseudofunctor.StrongTrans

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

noncomputable section
namespace map

/-- The induced map commutes with the first pseudopullback projection. -/
def fstIso (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [R.IsBilimit] :
    LeftLegDiagonal.map P Q R ≫ R.fst ≅ Q.fst ≫ P.fst :=
  PseudoPullbackCone.mapCospan.fstIso Q R (transform P) ≪≫
    whiskerLeftIso Q.fst
      (eqToIso (CospanTransform.mk_left P.fst P.fst g P.iso P.iso))

/-- The induced map commutes with the second pseudopullback projection. -/
def sndIso (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [R.IsBilimit] :
    LeftLegDiagonal.map P Q R ≫ R.snd ≅ Q.snd ≫ P.fst :=
  PseudoPullbackCone.mapCospan.sndIso Q R (transform P) ≪≫
    whiskerLeftIso Q.snd
      (eqToIso (CospanTransform.mk_right P.fst P.fst g P.iso P.iso))

end map

namespace source

/-- The composite through the source relative diagonal and the induced map presents the first
projection `P.fst` of the common cone.
-/
def fstIso (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (sourceDiagonal P Q ≫ LeftLegDiagonal.map P Q R) ≫ R.fst ≅ P.fst :=
  α_ (sourceDiagonal P Q) (LeftLegDiagonal.map P Q R) R.fst ≪≫
    whiskerLeftIso (sourceDiagonal P Q) (map.fstIso P Q R) ≪≫
    (α_ (sourceDiagonal P Q) Q.fst P.fst).symm ≪≫
    whiskerRightIso (sourceDiagonal.fstIso P Q) P.fst ≪≫
    λ_ P.fst

/-- The composite through the source relative diagonal and the induced map presents the second
projection `P.fst` of the common cone.
-/
def sndIso (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (sourceDiagonal P Q ≫ LeftLegDiagonal.map P Q R) ≫ R.snd ≅ P.fst :=
  α_ (sourceDiagonal P Q) (LeftLegDiagonal.map P Q R) R.snd ≪≫
    whiskerLeftIso (sourceDiagonal P Q) (map.sndIso P Q R) ≪≫
    (α_ (sourceDiagonal P Q) Q.snd P.fst).symm ≪≫
    whiskerRightIso (sourceDiagonal.sndIso P Q) P.fst ≪≫
    λ_ P.fst

end source

namespace target

/-- The composite through `P.fst` and the target relative diagonal presents the first
projection `P.fst` of the common cone.
-/
def fstIso (P : PseudoPullbackCone f g) (R : PseudoPullbackCone f f)
    [R.IsBilimit] :
    (P.fst ≫ targetDiagonal R) ≫ R.fst ≅ P.fst :=
  α_ P.fst (targetDiagonal R) R.fst ≪≫
    whiskerLeftIso P.fst (targetDiagonal.fstIso R) ≪≫
    ρ_ P.fst

/-- The composite through `P.fst` and the target relative diagonal presents the second
projection `P.fst` of the common cone.
-/
def sndIso (P : PseudoPullbackCone f g) (R : PseudoPullbackCone f f)
    [R.IsBilimit] :
    (P.fst ≫ targetDiagonal R) ≫ R.snd ≅ P.fst :=
  α_ P.fst (targetDiagonal R) R.snd ≪≫
    whiskerLeftIso P.fst (targetDiagonal.sndIso R) ≪≫
    ρ_ P.fst

end target

namespace presentation.left

/-- Vertexwise presentation of the composite through the source relative diagonal as the
common cone `cone P`.
-/
def app (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    ∀ j : LocallyDiscrete Limits.WalkingCospan,
      ((R.toPseudoCone.comparison P.pt).obj
          (sourceDiagonal P Q ≫ LeftLegDiagonal.map P Q R)).app j ≅
        (cone P).toPseudoCone.π.app j
  | ⟨Limits.WalkingCospan.one⟩ =>
      (α_ (sourceDiagonal P Q ≫ LeftLegDiagonal.map P Q R) R.fst f).symm ≪≫
        whiskerRightIso (source.fstIso P Q R) f
  | ⟨Limits.WalkingCospan.left⟩ => source.fstIso P Q R
  | ⟨Limits.WalkingCospan.right⟩ => source.sndIso P Q R

/-- The vertexwise source-composite presentation satisfies walking-cospan naturality. -/
theorem naturality (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    ∀ {a b : LocallyDiscrete Limits.WalkingCospan} (h : a ⟶ b),
      (Pseudofunctor.const
          (LocallyDiscrete Limits.WalkingCospan) P.pt).map h ◁
            (app P Q R b).hom ≫
          ((cone P).toPseudoCone.π.naturality h).hom =
        (((R.toPseudoCone.comparison P.pt).obj
            (sourceDiagonal P Q ≫ LeftLegDiagonal.map P Q R)).naturality h).hom ≫
          (app P Q R a).hom ▷ (cospan f f).map h := sorry

/-- The complete invertible modification presenting the source composite as `cone P`. -/
def iso (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (R.toPseudoCone.comparison P.pt).obj
        (sourceDiagonal P Q ≫ LeftLegDiagonal.map P Q R) ≅
      (cone P).toPseudoCone.π :=
  Pseudofunctor.StrongTrans.isoMk (app P Q R) (naturality P Q R)

end presentation.left

namespace presentation.right

/-- Vertexwise presentation of the composite through `P.fst` and the target relative diagonal
as the common cone `cone P`.
-/
def app (P : PseudoPullbackCone f g) (R : PseudoPullbackCone f f)
    [R.IsBilimit] :
    ∀ j : LocallyDiscrete Limits.WalkingCospan,
      ((R.toPseudoCone.comparison P.pt).obj
          (P.fst ≫ targetDiagonal R)).app j ≅
        (cone P).toPseudoCone.π.app j
  | ⟨Limits.WalkingCospan.one⟩ =>
      (α_ (P.fst ≫ targetDiagonal R) R.fst f).symm ≪≫
        whiskerRightIso (target.fstIso P R) f
  | ⟨Limits.WalkingCospan.left⟩ => target.fstIso P R
  | ⟨Limits.WalkingCospan.right⟩ => target.sndIso P R

/-- The vertexwise target-composite presentation satisfies walking-cospan naturality. -/
theorem naturality (P : PseudoPullbackCone f g) (R : PseudoPullbackCone f f)
    [R.IsBilimit] :
    ∀ {a b : LocallyDiscrete Limits.WalkingCospan} (h : a ⟶ b),
      (Pseudofunctor.const
          (LocallyDiscrete Limits.WalkingCospan) P.pt).map h ◁
            (app P R b).hom ≫
          ((cone P).toPseudoCone.π.naturality h).hom =
        (((R.toPseudoCone.comparison P.pt).obj
            (P.fst ≫ targetDiagonal R)).naturality h).hom ≫
          (app P R a).hom ▷ (cospan f f).map h := sorry

/-- The complete invertible modification presenting the target composite as `cone P`. -/
def iso (P : PseudoPullbackCone f g) (R : PseudoPullbackCone f f)
    [R.IsBilimit] :
    (R.toPseudoCone.comparison P.pt).obj (P.fst ≫ targetDiagonal R) ≅
      (cone P).toPseudoCone.π :=
  Pseudofunctor.StrongTrans.isoMk (app P R) (naturality P R)

end presentation.right

namespace comparison

/-- The source composite is canonically isomorphic to the universal lift of the common cone. -/
def left (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    sourceDiagonal P Q ≫ LeftLegDiagonal.map P Q R ≅
      PseudoPullbackCone.lift (cone P) R :=
  PseudoPullbackCone.lift.uniqueIso (cone P) R
    (sourceDiagonal P Q ≫ LeftLegDiagonal.map P Q R)
    (presentation.left.iso P Q R)

/-- The target composite is canonically isomorphic to the universal lift of the common cone. -/
def right (P : PseudoPullbackCone f g) (R : PseudoPullbackCone f f)
    [R.IsBilimit] :
    P.fst ≫ targetDiagonal R ≅ PseudoPullbackCone.lift (cone P) R :=
  PseudoPullbackCone.lift.uniqueIso (cone P) R
    (P.fst ≫ targetDiagonal R) (presentation.right.iso P R)

end comparison

/-- The canonical comparison making the left-leg diagonal square `2`-commutative. -/
def iso (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    sourceDiagonal P Q ≫ LeftLegDiagonal.map P Q R ≅
      P.fst ≫ targetDiagonal R :=
  comparison.left P Q R ≪≫ (comparison.right P R).symm

/-- Stacks Project Lemma 04YR: the left-leg diagonal square determined by `P` and the two
chosen self-pseudopullbacks. -/
@[stacks 04YR "left-leg diagonal pseudo-pullback square"]
def square (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    PseudoPullbackCone (LeftLegDiagonal.map P Q R) (targetDiagonal R) where
  pt := P.pt
  fst := sourceDiagonal P Q
  snd := P.fst
  iso := LeftLegDiagonal.iso P Q R


end

end CategoryTheory.Bicategory.PseudoPullbackCone.LeftLegDiagonal
