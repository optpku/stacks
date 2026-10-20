/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Transitivity
public import ReasLib.AlgebraicGeometry.RingedSite.Cotangent.DerivedBaseChange
public import ReasLib.RingTheory.CotangentComplex.Polynomial
public import Mathlib.RingTheory.Localization.Defs

/-!
# Localization of the cotangent complex

For compatible ring maps `A → A' → B`, invertibility of the canonical derived-tensor
comparison `B ⊗[A]^L A' → B` implies invertibility of the canonical comparison
`L_{B/A} ⟶ L_{B/A'}` in the derived category of `B`-modules.

For compatible localizations `Aₛ` of `A` at `S` and `Bₜ` of `B` at `T`, the
canonical comparison identifies `L_{Bₜ/Aₛ}` with `L_{B/A} ⊗_B Bₜ` in `D(Bₜ)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open RingedSite.Cotangent.Functoriality

universe u

namespace Algebra.CotangentComplex

/-- The commutative square of ring maps `A → A' → B` with identity on `B`. -/
theorem idCodomainCommSq (A A' B : Type u) [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B] :
    CommSq (CommRingCat.ofHom (algebraMap A A')) (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (algebraMap A' B)) (𝟙 (CommRingCat.of B)) :=
  sorry

/-- If the canonical comparison `B ⊗[A]^L A' → B` is invertible, then the canonical map
`L_{B/A} ⟶ L_{B/A'}` is invertible in the derived category of `B`-modules. -/
theorem toRelativeMap_isIso_of_derivedTensor (A A' B : Type u)
    [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
    (h : InducesDerivedTensorQuasiIso (idCodomainCommSq A A' B)) :
    IsIso (toRelativeMap A A' B) :=
  sorry

/-- Under a fact asserting invertibility of the canonical derived-tensor comparison,
the canonical change-of-base map of cotangent complexes is an isomorphism. -/
instance toRelativeMap_isIso_of_derivedTensor_of_fact (A A' B : Type u)
    [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
    [Fact (InducesDerivedTensorQuasiIso (idCodomainCommSq A A' B))] :
    IsIso (toRelativeMap A A' B) :=
  toRelativeMap_isIso_of_derivedTensor A A' B Fact.out

/-- Under the derived-tensor identity `B = B ⊗[A]^L A'`, the objects
`derived A B` and `derived A' B` are isomorphic in `D(B)`. -/
theorem isIsomorphic_derived_of_derivedTensor (A A' B : Type u)
    [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
    (h : InducesDerivedTensorQuasiIso (idCodomainCommSq A A' B)) :
    IsIsomorphic (derived A B) (derived A' B) :=
  sorry

/-- If the canonical multiplication comparison `B ⊗[A]^L B → B` is invertible,
the relative cotangent complex vanishes in the derived category of `B`-modules. -/
theorem isZero_derived_of_derivedTensor (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : InducesDerivedTensorQuasiIso (idCodomainCommSq A B B)) :
    IsZero (derived A B) :=
  sorry

/-- Under the derived-tensor identity `B = B ⊗[A]^L B`, every homology module of
`Algebra.cotangentComplex A B` vanishes. -/
theorem isZero_homology_of_derivedTensor (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : InducesDerivedTensorQuasiIso (idCodomainCommSq A B B)) {n : ℤ} :
    IsZero ((Algebra.cotangentComplex A B).homology n) :=
  sorry

/-- For compatible localizations `Aₛ` of `A` at `S` and `Bₜ` of `B` at `T`,
the canonical composite `L_{B/A} ⊗_B Bₜ ⟶ L_{Bₜ/A} ⟶ L_{Bₜ/Aₛ}` is invertible
in the derived category of `Bₜ`-modules. -/
@[stacks 08SF]
theorem tensorMap_comp_toRelativeMap_isIso (A B Aₛ Bₜ : Type u)
    [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₜ]
    [Algebra A B] [Algebra A Aₛ] [Algebra B Bₜ] [Algebra Aₛ Bₜ] [Algebra A Bₜ]
    [IsScalarTower A B Bₜ] [IsScalarTower A Aₛ Bₜ]
    (S : Submonoid A) (T : Submonoid B) [IsLocalization S Aₛ] [IsLocalization T Bₜ]
    (hST : S ≤ T.comap (algebraMap A B)) :
    IsIso (tensorMap A B Bₜ ≫ toRelativeMap A Aₛ Bₜ) :=
  sorry

/-- Under localization of `A` at `S` and of `B` at `T` with `S` mapping into `T`,
the objects `derived Aₛ Bₜ` and `tensor A B Bₜ` are isomorphic in `D(Bₜ)`. -/
theorem isIsomorphic_derived_tensor_of_isLocalization (A B Aₛ Bₜ : Type u)
    [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₜ]
    [Algebra A B] [Algebra A Aₛ] [Algebra B Bₜ] [Algebra Aₛ Bₜ] [Algebra A Bₜ]
    [IsScalarTower A B Bₜ] [IsScalarTower A Aₛ Bₜ]
    (S : Submonoid A) (T : Submonoid B) [IsLocalization S Aₛ] [IsLocalization T Bₜ]
    (hST : S ≤ T.comap (algebraMap A B)) :
    IsIsomorphic (derived Aₛ Bₜ) (tensor A B Bₜ) :=
  sorry

end Algebra.CotangentComplex
