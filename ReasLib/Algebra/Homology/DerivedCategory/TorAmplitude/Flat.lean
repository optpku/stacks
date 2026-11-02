/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FlatResolution
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat derived modules in one degree

This leaf separates the intrinsic flat-degree predicate from the source-facing
existential packaging and records the module-category upper Tor-amplitude
bridge.
@stack 0H85
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

variable {R : Type u} [CommRing R]

/-- The object property of being isomorphic to a flat `R`-module placed in
degree `n`. -/
@[stacks 0H85 "flat module in one derived degree"]
def flatInDegree (n : ℤ) : ObjectProperty (DerivedCategory (ModuleCat R)) :=
  fun K ↦ ∃ N : ModuleCat R, Module.Flat R N ∧
    IsIsomorphic K ((DerivedCategory.singleFunctor (ModuleCat R) n).obj N)

/-- Object-level spelling of membership in the flat-degree property. -/
@[stacks 0H85 "flat module in one derived degree, object-level spelling"]
abbrev IsFlatInDegree (K : DerivedCategory (ModuleCat R)) (n : ℤ) : Prop :=
  flatInDegree n K

/-- Being a flat module in one degree is invariant under isomorphism in the
derived category. -/
@[stacks 0H85 "flat degree is invariant under derived isomorphism"]
instance flatInDegree_isClosedUnderIsomorphisms (n : ℤ) :
    (flatInDegree (R := R) n).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro K L e ⟨N, hN, ⟨f⟩⟩
    exact ⟨N, hN, ⟨e.symm ≪≫ f⟩⟩
/- Proof strategy: transport the module-and-isomorphism witness through the supplied derived
isomorphism, composing it with the witness isomorphism in `flatInDegree`. -/

/-- For module categories, testing derived tensors against degree-zero modules
does not change an upper cohomological bound. -/
@[stacks 0H85 "upper Tor-amplitude is an upper cohomological bound"]
theorem hasTorAmplitudeLE_iff_isLE
    (K : DerivedCategory (ModuleCat R)) (b : ℤ) :
    HasTorAmplitudeLE R K b ↔ K.IsLE b := sorry
/- Proof strategy: test the Tor-amplitude condition on the tensor unit for the forward
implication; for the converse use right t-exactness of derived tensor with a degree-zero
module together with the upper bound on `K`. -/

/-- A Tor-amplitude interval with equal endpoints is equivalent to being a flat
module in that degree. -/
@[stacks 0H85 "zero-width Tor-amplitude and flat degree"]
theorem hasTorAmplitudeIn_self_iff_isFlatInDegree
    (K : DerivedCategory (ModuleCat R)) (n : ℤ) :
    HasTorAmplitudeIn R K n n ↔ IsFlatInDegree K n := sorry
/- Proof strategy: use the equal lower and upper bounds to identify `K` with its only nonzero
homology module placed in degree `n`; the remaining Tor-amplitude condition is precisely
flatness of that homology module.  Conversely tensor the displayed flat single-degree model. -/

/-- The upper Tor-amplitude supplied by an upper cohomological bound. -/
@[stacks 0H85 "upper cohomological bounds give upper Tor-amplitude"]
theorem IsLE.hasTorAmplitudeLE
    {K : DerivedCategory (ModuleCat R)} {b : ℤ} (hK : K.IsLE b) :
    HasTorAmplitudeLE R K b :=
  (hasTorAmplitudeLE_iff_isLE K b).mpr hK
/- Proof strategy: apply the reverse implication of `hasTorAmplitudeLE_iff_isLE`. -/

/-- An upper Tor-amplitude bound is already an upper cohomological bound in a
module category. -/
@[stacks 0H85 "upper Tor-amplitude gives an upper cohomological bound"]
theorem HasTorAmplitudeLE.isLE
    {K : DerivedCategory (ModuleCat R)} {b : ℤ}
    (hK : HasTorAmplitudeLE R K b) : K.IsLE b :=
  (hasTorAmplitudeLE_iff_isLE K b).mp hK
/- Proof strategy: apply the forward implication of `hasTorAmplitudeLE_iff_isLE`. -/

/-- The canonical flat-degree witness extracted from a zero-width
Tor-amplitude interval. -/
@[stacks 0H85 "zero-width Tor-amplitude gives a flat degree"]
theorem HasTorAmplitudeIn.isFlatInDegree
    {K : DerivedCategory (ModuleCat R)} {n : ℤ}
    (hK : HasTorAmplitudeIn R K n n) : IsFlatInDegree K n :=
  (hasTorAmplitudeIn_self_iff_isFlatInDegree K n).mp hK
/- Proof strategy: apply the forward implication of
`hasTorAmplitudeIn_self_iff_isFlatInDegree`. -/

/-- A flat module in one degree has the corresponding zero-width Tor-amplitude. -/
@[stacks 0H85 "a flat degree gives zero-width Tor-amplitude"]
theorem IsFlatInDegree.hasTorAmplitudeIn
    {K : DerivedCategory (ModuleCat R)} {n : ℤ}
    (hK : IsFlatInDegree K n) : HasTorAmplitudeIn R K n n :=
  (hasTorAmplitudeIn_self_iff_isFlatInDegree K n).mpr hK
/- Proof strategy: apply the reverse implication of
`hasTorAmplitudeIn_self_iff_isFlatInDegree`. -/

end CategoryTheory.DerivedCategory
