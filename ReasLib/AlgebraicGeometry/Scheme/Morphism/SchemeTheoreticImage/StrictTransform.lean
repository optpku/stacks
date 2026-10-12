/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Lift
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.Blowup

/-!
# Scheme-theoretic images and strict transforms

This file constructs the canonical embedding of the strict transform of a scheme-theoretic
image into a blown-up fiber product and compares it with the image of the lifted morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/-- The strict-transform projections define a morphism into `X' ×_S Y`. -/
theorem strictTransformImageMap_condition
    {S X Y V X' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (q : V ⟶ pullback f g) (b : X' ⟶ X) (I : X.IdealSheafData) :
    strictTransformSnd b (I.comap b) (q.imageι ≫ pullback.fst f g) ≫ (b ≫ f) =
      (strictTransformFst b (I.comap b) (q.imageι ≫ pullback.fst f g) ≫
        q.imageι ≫ pullback.snd f g) ≫ g := sorry

/-- The canonical embedding of the strict transform of `q.image` into `X' ×_S Y`. -/
noncomputable def strictTransformImageMap
    {S X Y V X' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (q : V ⟶ pullback f g) (b : X' ⟶ X) (I : X.IdealSheafData) :
    strictTransform b (I.comap b) (q.imageι ≫ pullback.fst f g) ⟶
      pullback (b ≫ f) g :=
  pullback.lift
    (strictTransformSnd b (I.comap b) (q.imageι ≫ pullback.fst f g))
    (strictTransformFst b (I.comap b) (q.imageι ≫ pullback.fst f g) ≫
      q.imageι ≫ pullback.snd f g)
    (strictTransformImageMap_condition f g q b I)

/-- The first projection of the strict-transform embedding is its projection to `X'`. -/
@[reassoc]
theorem strictTransformImageMap_fst
    {S X Y V X' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (q : V ⟶ pullback f g) (b : X' ⟶ X) (I : X.IdealSheafData) :
    strictTransformImageMap f g q b I ≫ pullback.fst (b ≫ f) g =
      strictTransformSnd b (I.comap b) (q.imageι ≫ pullback.fst f g) := sorry

/-- The second projection of the strict-transform embedding is induced by the projection of
`q.image` to `Y`. -/
@[reassoc]
theorem strictTransformImageMap_snd
    {S X Y V X' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (q : V ⟶ pullback f g) (b : X' ⟶ X) (I : X.IdealSheafData) :
    strictTransformImageMap f g q b I ≫ pullback.snd (b ≫ f) g =
      strictTransformFst b (I.comap b) (q.imageι ≫ pullback.fst f g) ≫
        q.imageι ≫ pullback.snd f g := sorry

/-- The strict-transform map into the blown-up pullback is a closed immersion. -/
instance instIsClosedImmersionStrictTransformImageMap
    {S X Y V X' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (q : V ⟶ pullback f g) (b : X' ⟶ X) (I : X.IdealSheafData) :
    IsClosedImmersion (strictTransformImageMap f g q b I) := sorry

/-- The scheme-theoretic image of the canonical lift of a quasi-compact morphism to
`X' ×_S Y` is isomorphic over that fiber product to the strict transform of its image in
`X ×_S Y`. -/
theorem image_liftAdmissible_isomorphic_strictTransform
    {S X Y V X' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (q : V ⟶ pullback f g) [QuasiCompact q]
    (U : X.Opens) (b : X' ⟶ X) (I : X.IdealSheafData)
    [IsAdmissibleBlowupCenter U b I]
    (hU : Set.range (q ≫ pullback.fst f g).base ⊆ Set.range U.ι.base) :
    Nonempty
      (Over.mk (liftAdmissiblePullback f g q U b I hU).imageι ≅
        Over.mk (strictTransformImageMap f g q b I)) := sorry

end Scheme.Hom

end AlgebraicGeometry
