module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine

/-!
# Higher direct images along affine morphisms

Positive-degree higher direct images of quasi-coherent modules along affine morphisms vanish.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Positive-degree higher direct images of a quasi-coherent module along an affine morphism of
algebraic spaces vanish. -/
theorem higherDirectImage_isZero_of_affine (f : X ⟶ Y) [Affine f]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ) (hi : 0 < i) :
    IsZero (higherDirectImage f ℱ i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
