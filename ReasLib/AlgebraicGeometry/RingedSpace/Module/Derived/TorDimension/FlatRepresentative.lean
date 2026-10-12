/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.FlatRepresentative
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Flat representatives on ringed spaces

This file specializes the generic flat-representative object property to modules on a ringed
space and relates it to the canonical derived tensor product.
-/

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

/-- The object property of admitting a termwise-flat `𝒪_X`-module representative supported in
`[a, b]`. -/
abbrev flatRepresentativeIn (a b : ℤ) : ObjectProperty (ModuleDerived X) :=
  DerivedCategory.flatRepresentativeIn (C := Modules X) a b

/-- A derived `𝒪_X`-module admits a termwise-flat cochain representative supported in
`[a, b]`. -/
abbrev HasFlatRepresentativeIn (E : ModuleDerived X) (a b : ℤ) : Prop :=
  flatRepresentativeIn (X := X) a b E

/-- The ringed-space flat-representative predicate unfolds to a supported termwise-flat complex
of `𝒪_X`-modules. -/
theorem hasFlatRepresentativeIn_iff (E : ModuleDerived X) (a b : ℤ) :
    HasFlatRepresentativeIn E a b ↔
      ∃ (K : CochainComplex (Modules X) ℤ) (_ : E ≅ DerivedCategory.Q.obj K),
        K.IsStrictlyGE a ∧ K.IsStrictlyLE b ∧ HomologicalComplex.IsTermwiseFlat K := sorry

/-- A derived `𝒪_X`-module has Tor-amplitude in `[a, b]` exactly when it admits a
termwise-flat representative supported in `[a, b]`. -/
@[stacks 08CI]
theorem hasTorAmplitudeIn_iff_hasFlatRepresentativeIn
    (E : ModuleDerived X) (a b : ℤ) :
    RingedSpace.HasTorAmplitudeIn E a b ↔ HasFlatRepresentativeIn E a b := sorry

/-- A Tor-amplitude bound on a ringed space gives a flat representative in the same interval. -/
theorem hasFlatRepresentativeIn_of_hasTorAmplitudeIn
    {E : ModuleDerived X} {a b : ℤ}
    (hE : RingedSpace.HasTorAmplitudeIn E a b) : HasFlatRepresentativeIn E a b := sorry

/-- A flat representative in `[a, b]` gives the corresponding Tor-amplitude bound. -/
theorem HasFlatRepresentativeIn.hasTorAmplitudeIn
    {E : ModuleDerived X} {a b : ℤ}
    (hE : HasFlatRepresentativeIn E a b) : RingedSpace.HasTorAmplitudeIn E a b := sorry

/-- A derived `𝒪_X`-module has a flat representative concentrated in degree `n` exactly when
it is isomorphic to a flat module sheaf placed in degree `n`. -/
theorem hasFlatRepresentativeIn_self_iff_exists_flat (E : ModuleDerived X) (n : ℤ) :
    HasFlatRepresentativeIn E n n ↔
      ∃ F : X.Modules, F.IsFlat ∧
        IsIsomorphic E ((DerivedCategory.singleFunctor X.Modules n).obj F) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
