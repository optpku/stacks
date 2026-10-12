/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.StrictTransform
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic

/-!
# Strict transforms and blowups

This file relates the strict transform of a scheme to the blowup of the scheme in the
inverse-image center and records the corresponding comparison for module strict transforms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The canonical projection from a strict-transform scheme to the original scheme. -/
noncomputable def strictTransformFst
    {S S' X : Scheme.{u}} (b : S' ⟶ S) (E : S'.IdealSheafData) (f : X ⟶ S) :
    strictTransform b E f ⟶ X :=
  (strictTransformIdealSheafData b E f).subschemeι ≫ pullback.fst f b

/-- The canonical projection from a strict-transform scheme to the transformed base. -/
noncomputable def strictTransformSnd
    {S S' X : Scheme.{u}} (b : S' ⟶ S) (E : S'.IdealSheafData) (f : X ⟶ S) :
    strictTransform b E f ⟶ S' :=
  (strictTransformIdealSheafData b E f).subschemeι ≫ pullback.snd f b

/-- The two canonical projections from a strict-transform scheme form a commutative square. -/
theorem strictTransform_condition
    {S S' X : Scheme.{u}} (b : S' ⟶ S) (E : S'.IdealSheafData) (f : X ⟶ S) :
    strictTransformFst b E f ≫ f = strictTransformSnd b E f ≫ b := by
  simp only [strictTransformFst, strictTransformSnd, Category.assoc]
  rw [pullback.condition]

/-- The canonical map from the relative strict-transform ambient scheme to the original
strict-transform ambient scheme. -/
noncomputable def strictTransformRelativeMap
    {S S' X : Scheme.{u}} (b : S' ⟶ S) (E : S'.IdealSheafData) (f : X ⟶ S) :
    strictTransformAmbient (strictTransformFst b E f) (𝟙 X) ⟶ strictTransformAmbient b f :=
  pullback.map (𝟙 X) (strictTransformFst b E f) f b
    (𝟙 X) (strictTransformSnd b E f) f rfl (strictTransform_condition b E f)

/-- The canonical projection from the strict transform along a blowup is the blowup of the
source scheme in the inverse-image center. -/
theorem strictTransformFst_isBlowup
    {S S' X : Scheme.{u}} (I : S.IdealSheafData) (b : S' ⟶ S) [IsBlowup b I]
    (f : X ⟶ S) :
    IsBlowup (strictTransformFst b (I.comap b) f) (I.comap f) := sorry

/-- The canonical projection from the strict transform along a blowup carries its canonical
blowup structure. -/
instance instIsBlowupStrictTransformFst
    {S S' X : Scheme.{u}} (I : S.IdealSheafData) (b : S' ⟶ S) [IsBlowup b I]
    (f : X ⟶ S) :
    IsBlowup (strictTransformFst b (I.comap b) f) (I.comap f) :=
  strictTransformFst_isBlowup I b f

namespace Scheme.Modules

/-- A quasicoherent module's strict transform along a blowup is isomorphic to the pushforward
of its strict transform relative to the induced blowup of the source scheme. -/
theorem strictTransformModule_isomorphic_pushforward_relativeStrictTransform
    {S S' X : Scheme.{u}} (I : S.IdealSheafData) (b : S' ⟶ S) [IsBlowup b I]
    (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIsomorphic
      (strictTransformModule b (I.comap b) f ℱ)
      ((Scheme.Modules.pushforward (strictTransformRelativeMap b (I.comap b) f)).obj
        (strictTransformModule
          (strictTransformFst b (I.comap b) f)
          ((I.comap f).comap (strictTransformFst b (I.comap b) f)) (𝟙 X) ℱ)) := sorry

end Scheme.Modules

end AlgebraicGeometry
