module

public import stacks_project.Chap92.«92_7_0_1_Triangle»
import Mathlib.RingTheory.Localization.Defs
import Mathlib.Tactic.CrossRefAttribute

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

namespace Algebra.CotangentComplex

/-- Lemma 92.8.6. Let `A → B` be a ring map and `S ⊆ A`, `T ⊆ B` multiplicative
subsets such that `S` maps into `T`. Then `L_{T⁻¹B / S⁻¹A} = L_{B/A} ⊗_B T⁻¹B`
in `D(T⁻¹B)`, as invertibility of `tensorMap A B Bₜ ≫ toRelativeMap A Aₛ Bₜ`. -/
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
