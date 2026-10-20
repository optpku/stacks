/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage

/-!
# Integer-degree higher direct images

Higher direct images of module sheaves are extended by the zero module sheaf in negative degrees.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (F : X.Modules)

/-- The integer-degree higher direct image of a module sheaf, zero in negative degrees. -/
def higherDirectImageInt (q : ℤ) : Y.Modules :=
  match q with
  | .ofNat n => higherDirectImage f F n
  | .negSucc _ => (HasZeroObject.zero' Y.Modules).zero

/-- Integer-degree higher direct images agree with ordinary higher direct images in
nonnegative degrees. -/
@[simp]
theorem higherDirectImageInt_ofNat (n : ℕ) :
    higherDirectImageInt f F (Int.ofNat n) = higherDirectImage f F n :=
  rfl

/-- Integer-degree higher direct images are the zero module sheaf in negative degrees. -/
@[simp]
theorem higherDirectImageInt_negSucc (n : ℕ) :
    higherDirectImageInt f F (Int.negSucc n) = (HasZeroObject.zero' Y.Modules).zero :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
