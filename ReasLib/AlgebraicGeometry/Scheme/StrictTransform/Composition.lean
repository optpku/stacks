module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.Blowup
import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.EffectiveCartier

/-!
# Composition of strict transforms

This file compares strict transforms along two successive blowups with the strict transform
along their composite.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme.Modules

/-- If two successive blowups compose to the blowup in a center whose support is the union of
the first center and the image of the second, then the direct strict transform of a
quasicoherent module is isomorphic to its iterated strict transform after the canonical
pullback-pasting transport. -/
theorem strictTransformModule_isomorphic_pushforward_iteratedStrictTransform
    {S S' S'' X : Scheme.{u}} (Z : S.IdealSheafData)
    (b : S' ⟶ S) [IsBlowup b Z]
    (Z' : S'.IdealSheafData) (b' : S'' ⟶ S') [IsBlowup b' Z']
    (Y : S.IdealSheafData)
    (hY : (Y.support : Set S) = (Z.support : Set S) ∪ b.base '' (Z'.support : Set S'))
    [IsBlowup (b' ≫ b) Y]
    (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIsomorphic
      (strictTransformModule (b' ≫ b) (Y.comap (b' ≫ b)) f ℱ)
      ((Scheme.Modules.pushforward (pullbackLeftPullbackSndIso f b b').hom).obj
        (strictTransformModule b' (Z'.comap b') (pullback.snd f b)
          (strictTransformModule b (Z.comap b) f ℱ))) := sorry

end Scheme.Modules

/-- If two successive blowups compose to the blowup in a center whose support is the union of
the first center and the image of the second, then the direct strict transform of a scheme is
isomorphic to its iterated strict transform. -/
theorem strictTransform_isomorphic_iteratedStrictTransform
    {S S' S'' X : Scheme.{u}} (Z : S.IdealSheafData)
    (b : S' ⟶ S) [IsBlowup b Z]
    (Z' : S'.IdealSheafData) (b' : S'' ⟶ S') [IsBlowup b' Z']
    (Y : S.IdealSheafData)
    (hY : (Y.support : Set S) = (Z.support : Set S) ∪ b.base '' (Z'.support : Set S'))
    [IsBlowup (b' ≫ b) Y]
    (f : X ⟶ S) :
    IsIsomorphic
      (strictTransform (b' ≫ b) (Y.comap (b' ≫ b)) f)
      (strictTransform b' (Z'.comap b') (strictTransformSnd b (Z.comap b) f)) := sorry

end AlgebraicGeometry
