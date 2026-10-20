module

public import ReasLib.AlgebraicGeometry.Scheme.StrictTransform
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat

/-!
# Flat strict transforms

Flatness along the center of a blowup makes the canonical comparisons from pullbacks to strict
transforms invertible.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace Scheme.Modules

/-- If a quasicoherent module is flat over the base at every point lying over the center of a
blowup, then the canonical quotient map from its pullback to its strict transform is an
isomorphism. -/
theorem strictTransformπ_isIso_of_flatOverAt_over_center
    {S S' X : Scheme.{u}} (I : S.IdealSheafData) (b : S' ⟶ S) [IsBlowup b I]
    (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (hflat : ∀ x : X, f.base x ∈ I.support → flatOverAt ℱ f x) :
    IsIso (strictTransformπ b (I.comap b) f ℱ) := sorry

end Scheme.Modules

/-- If a morphism is flat over the base at every point lying over the center of a blowup, then
the canonical closed immersion of its strict transform into the ambient base change is an
isomorphism. -/
theorem strictTransform_subschemeι_isIso_of_flatAt_over_center
    {S S' X : Scheme.{u}} (I : S.IdealSheafData) (b : S' ⟶ S) [IsBlowup b I]
    (f : X ⟶ S) (hflat : ∀ x : X, f.base x ∈ I.support → Scheme.Hom.flatAt f x) :
    IsIso (strictTransformIdealSheafData b (I.comap b) f).subschemeι := sorry

end AlgebraicGeometry
