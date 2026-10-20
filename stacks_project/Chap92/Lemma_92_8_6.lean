/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Localization
import StacksCheckRecall

/-!
# Localization of the cotangent complex

If `A → B` is a ring map and `S ⊆ A`, `T ⊆ B` are multiplicative subsets with
`S` mapping into `T`, the comparison `tensorMap A B Bₜ ≫ toRelativeMap A Aₛ Bₜ`
identifies `L_{T⁻¹B / S⁻¹A}` with `L_{B/A} ⊗_B T⁻¹B` in `D(T⁻¹B)`.
-/

@[expose] public section

open Algebra.CotangentComplex
open CategoryTheory

universe u

/- Lemma 92.8.6. Let `A → B` be a ring map and `S ⊆ A`, `T ⊆ B` multiplicative
subsets such that `S` maps into `T`. Then `L_{T⁻¹B / S⁻¹A} = L_{B/A} ⊗_B T⁻¹B`
in `D(T⁻¹B)`, as invertibility of `tensorMap A B Bₜ ≫ toRelativeMap A Aₛ Bₜ`. -/
@[stacks 08SF] #check (Algebra.CotangentComplex.tensorMap_comp_toRelativeMap_isIso :
  ∀ (A B Aₛ Bₜ : Type u)
    [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₜ]
    [Algebra A B] [Algebra A Aₛ] [Algebra B Bₜ] [Algebra Aₛ Bₜ] [Algebra A Bₜ]
    [IsScalarTower A B Bₜ] [IsScalarTower A Aₛ Bₜ]
    (S : Submonoid A) (T : Submonoid B) [IsLocalization S Aₛ] [IsLocalization T Bₜ]
    (hST : S ≤ T.comap (algebraMap A B)),
    IsIso (tensorMap A B Bₜ ≫ toRelativeMap A Aₛ Bₜ))

/- Under localization of `A` at `S` and of `B` at `T` with `S` mapping into `T`,
the objects `derived Aₛ Bₜ` and `tensor A B Bₜ` are isomorphic in `D(Bₜ)`. -/
#check (Algebra.CotangentComplex.isIsomorphic_derived_tensor_of_isLocalization :
  ∀ (A B Aₛ Bₜ : Type u)
    [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₜ]
    [Algebra A B] [Algebra A Aₛ] [Algebra B Bₜ] [Algebra Aₛ Bₜ] [Algebra A Bₜ]
    [IsScalarTower A B Bₜ] [IsScalarTower A Aₛ Bₜ]
    (S : Submonoid A) (T : Submonoid B) [IsLocalization S Aₛ] [IsLocalization T Bₜ]
    (hST : S ≤ T.comap (algebraMap A B)),
    IsIsomorphic (derived Aₛ Bₜ) (tensor A B Bₜ))
