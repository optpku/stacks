/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.RegularBaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DerivedCategory.CechCompletion
open CategoryTheory.DerivedCategory.LocalCohomology.BaseChange

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

/- Lemma 47.10.3 (1): after derived extension of scalars along `f`, the canonical
comparison from `RΓ_I(A)` to `RΓ_Z(A)` is an isomorphism in `D(B)`. -/
@[stacks 0957] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.regularIdealToClosedSupportBaseChangeIsIso :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      (f : A →+* B) (I : Ideal A)
      (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
      (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ),
      IsIso
        ((ModuleCat.derivedExtensionOfScalars f).map
          ((IdealPowerTorsion.inclusion I).map
            ((idealToClosedSupport I (Ideal.fg_of_isNoetherianRing I) RΓZ hRΓZ).app
              regular))))

/- Lemma 47.10.3 (2): the canonical base-change comparison identifies
`RΓ_Z(A) ⊗_A^L B` with `RΓ_Y(B)` in `D(B)`, where `Y = V(I.map f)`. -/
@[stacks 0957] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.regularClosedSupportBaseChangeIsIso :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      (f : A →+* B) (I : Ideal A)
      (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
      (RΓY : DerivedCategory (ModuleCat B) ⥤ IdealPowerTorsion (I.map f))
      (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ)
      (hRΓY : IdealPowerTorsion.inclusion (I.map f) ⊣ RΓY),
      IsIso
        ((IdealPowerTorsion.inclusion (I.map f)).map
          ((comparison f I (Ideal.fg_of_isNoetherianRing I) RΓZ RΓY hRΓZ hRΓY).app
            regular)))

/- Lemma 47.10.3 (3): for the target-ring object presented as the derived scalar
extension of the regular `A`-module, the canonical comparison identifies
`RΓ_{I.map f}(B)` with `RΓ_Y(B)` in `D(B)`. -/
@[stacks 0957] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.regularIdealToClosedSupportOverTargetIsIso :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      (f : A →+* B) (I : Ideal A)
      (RΓY : DerivedCategory (ModuleCat B) ⥤ IdealPowerTorsion (I.map f))
      (hRΓY : IdealPowerTorsion.inclusion (I.map f) ⊣ RΓY),
      IsIso
        ((IdealPowerTorsion.inclusion (I.map f)).map
          ((idealToClosedSupport (I.map f)
            (Ideal.fg_of_isNoetherianRing (I.map f)) RΓY hRΓY).app
              ((ModuleCat.derivedExtensionOfScalars f).obj regular))))

end CategoryTheory.DerivedCategory.LocalCohomology
