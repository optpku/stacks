/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Flat.Availability
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfectness detected on a finite principal localization cover

@stack 066Y

The localization objects are expressed through the explicit derived extension-of-scalars
functor.  This keeps the ring map and the finite cover visible to downstream callers and avoids a
chapter-local tensor notation or ambient algebra instance.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe uR uI v

namespace CategoryTheory.DerivedCategory.IsPerfect

variable {R : Type uR} [CommRing R]

/-- Lemma 15.75.12 (Stacks `066Y`): perfectness descends from a finite principal localization
cover generating the unit ideal. -/
@[stacks 066Y "perfectness on a finite principal localization cover"]
theorem of_localizationAway_unitIdeal
    {ι : Type uI} [Finite ι] (f : ι → R)
    (hunit : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{v, uR} R))
    (hloc : ∀ i,
      ((ModuleCat.derivedExtensionOfScalars.{uR, uR, v}
          (algebraMap R (Localization.Away (f i)))).obj K).IsPerfect) :
    K.IsPerfect := sorry

end CategoryTheory.DerivedCategory.IsPerfect
