/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Extension

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpace.Hom.IsFlat

noncomputable section

universe u

/- Lemma 36.13.8: if `F` is a perfect derived module on a quasi-compact open
subscheme of an affine scheme, then `F ⊞ F⟦1⟧` is the restriction of a perfect derived
module on the ambient scheme. -/
@[stacks 08EI] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.exists_biprod_shift_extension_of_isPerfect :
    ∀ {X U : Scheme.{u}} [IsAffine X]
      (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (F : RingedSpace.ModuleDerived U.toRingedSpace)
      (_ : RingedSpace.ModuleDerived.IsPerfect F),
      ∃ (P : RingedSpace.ModuleDerived X.toRingedSpace)
        (e : (exactPullback j.toShHom).mapDerivedCategory.obj P ≅ F ⊞ F⟦(1 : ℤ)⟧),
        RingedSpace.ModuleDerived.IsPerfect P)
