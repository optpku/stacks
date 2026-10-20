/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Extension.Support
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpace.Hom.IsFlat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.13.10: a perfect derived module on a quasi-compact open subscheme of an
affine scheme, supported over a closed subset with quasi-compact complement, admits a
perfect extension supported on that closed subset whose restriction is `F ⊞ F⟦(1 : ℤ)⟧`. -/
@[stacks 08EK] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.exists_supported_biprod_shift_extension :
    ∀ {X U : Scheme.{u}} [IsAffine X]
      (T : TopologicalSpace.Closeds X) (hT : IsCompact (T.compl : Set X))
      (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (F : RingedSpace.ModuleDerived U.toRingedSpace)
      (hF : RingedSpace.ModuleDerived.IsPerfect F)
      (hF_support : RingedSpace.ModuleDerived.IsSupportedOn F (j.base ⁻¹' (T : Set X))),
      ∃ (E : RingedSpace.ModuleDerived X.toRingedSpace)
        (e : (exactPullback j.toShHom).mapDerivedCategory.obj E ≅ F ⊞ F⟦(1 : ℤ)⟧),
        RingedSpace.ModuleDerived.IsPerfect E ∧
          RingedSpace.ModuleDerived.IsSupportedOn E (T : Set X))

end AlgebraicGeometry.Scheme.DerivedQCoh
