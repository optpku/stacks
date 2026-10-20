/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LeftLegDiagonal.Presentation

/-!
# Central comparisons for left-leg diagonal squares

This leaf exposes the common-target components of the induced map and of the two composite
presentations. It complements the endpoint comparisons in `LeftLegDiagonal.Presentation` and
keeps downstream code independent of the concrete central walking-cospan vertex.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory.Bicategory.PseudoPullbackCone.LeftLegDiagonal

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

noncomputable section

namespace map

/-- The induced map commutes with the central leg of the target pseudopullback. -/
def baseIso (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [R.IsBilimit] :
    LeftLegDiagonal.map P Q R ≫ (R.fst ≫ f) ≅
      (Q.fst ≫ P.fst) ≫ f :=
  PseudoPullbackCone.mapCospan.baseIso Q R (transform P) ≪≫
    whiskerRightIso
      (whiskerLeftIso Q.fst
        (eqToIso (CospanTransform.mk_left P.fst P.fst g P.iso P.iso))) f

end map

namespace source

/-- The source composite presents the central leg `P.fst ≫ f` of the common cone. -/
def baseIso (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (sourceDiagonal P Q ≫ LeftLegDiagonal.map P Q R) ≫ (R.fst ≫ f) ≅
      P.fst ≫ f :=
  (α_ (sourceDiagonal P Q ≫ LeftLegDiagonal.map P Q R) R.fst f).symm ≪≫
    whiskerRightIso (source.fstIso P Q R) f

end source

namespace target

/-- The target composite presents the central leg `P.fst ≫ f` of the common cone. -/
def baseIso (P : PseudoPullbackCone f g) (R : PseudoPullbackCone f f)
    [R.IsBilimit] :
    (P.fst ≫ targetDiagonal R) ≫ (R.fst ≫ f) ≅ P.fst ≫ f :=
  (α_ (P.fst ≫ targetDiagonal R) R.fst f).symm ≪≫
    whiskerRightIso (target.fstIso P R) f

end target

end

end CategoryTheory.Bicategory.PseudoPullbackCone.LeftLegDiagonal
