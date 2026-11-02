/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Transitivity
public import ReasLib.RingTheory.CotangentComplex.DerivedBaseChange
public import ReasLib.RingTheory.CotangentComplex.Vanishing
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
  ⟨by
    apply CommRingCat.hom_ext
    exact (IsScalarTower.algebraMap_eq A A' B).symm.trans
      (RingHom.id_comp (algebraMap A B)).symm⟩

/-- If the canonical comparison `B ⊗[A]^L A' → B` is invertible, then the canonical map
`L_{B/A} ⟶ L_{B/A'}` is invertible in the derived category of `B`-modules. -/
theorem toRelativeMap_isIso_of_derivedTensor (A A' B : Type u)
    [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
    (h : InducesDerivedTensorQuasiIso (idCodomainCommSq A A' B)) :
    IsIso (toRelativeMap A A' B) :=
  by
    let f := map (algebraMap A B) (algebraMap A' B) (algebraMap A A') (RingHom.id B)
      (congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of B => f.hom)
        (idCodomainCommSq A A' B).w)
    have hi : IsIso (tensorComparison A B B ≫ DerivedCategory.Q.map f) :=
      mapDerived_isIso (idCodomainCommSq A A' B) h
    letI : IsIso (tensorComparison A B B) := tensorComparison_isIso A B B
    have hf : IsIso (DerivedCategory.Q.map f) :=
      (isIso_comp_left_iff (tensorComparison A B B) (DerivedCategory.Q.map f)).mp hi
    letI : IsIso (DerivedCategory.Q.map f) := hf
    let e₁ := ((Functor.mapHomologicalComplexIdIso (ModuleCat.{u} B)
        (ComplexShape.up ℤ)).app (Algebra.cotangentComplex A B)).symm
    let e₂ := ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId B)
        (ComplexShape.up ℤ)).app (Algebra.cotangentComplex A B)).symm
    letI : IsIso (DerivedCategory.Q.map e₁.hom) :=
      (DerivedCategory.Q.mapIso e₁).isIso_hom
    letI : IsIso (DerivedCategory.Q.map e₂.hom) :=
      (DerivedCategory.Q.mapIso e₂).isIso_hom
    change IsIso (DerivedCategory.Q.map (e₁.hom ≫ e₂.hom ≫ f))
    rw [Functor.map_comp, Functor.map_comp]
    apply (isIso_comp_left_iff (DerivedCategory.Q.map e₁.hom) _).mpr
    apply (isIso_comp_left_iff (DerivedCategory.Q.map e₂.hom) _).mpr
    exact hf

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
    IsIsomorphic (derived A B) (derived A' B) := by
  letI := toRelativeMap_isIso_of_derivedTensor A A' B h
  exact ⟨asIso (toRelativeMap A A' B)⟩

/-- If the canonical multiplication comparison `B ⊗[A]^L B → B` is invertible,
the relative cotangent complex vanishes in the derived category of `B`-modules. -/
theorem isZero_derived_of_derivedTensor (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : InducesDerivedTensorQuasiIso (idCodomainCommSq A B B)) :
    IsZero (derived A B) :=
  by
    letI : Algebra.IsPolynomial B B :=
      ⟨PEmpty.{u + 1}, ⟨(MvPolynomial.isEmptyAlgEquiv B PEmpty).symm⟩⟩
    letI : Subsingleton Ω[B⁄B] :=
      KaehlerDifferential.subsingleton_of_surjective B B Function.surjective_id
    obtain ⟨e⟩ := isIsomorphic_single_kaehler B B
    have hself : IsZero (derived B B) :=
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) (0 : ℤ)).map_isZero
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of B Ω[B⁄B]))).of_iso e
    obtain ⟨e'⟩ := isIsomorphic_derived_of_derivedTensor A B B h
    exact hself.of_iso e'

/-- Under the derived-tensor identity `B = B ⊗[A]^L B`, every homology module of
`Algebra.cotangentComplex A B` vanishes. -/
theorem isZero_homology_of_derivedTensor (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : InducesDerivedTensorQuasiIso (idCodomainCommSq A B B)) {n : ℤ} :
    IsZero ((Algebra.cotangentComplex A B).homology n) := by
  have hzero := (DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).map_isZero
    (isZero_derived_of_derivedTensor A B h)
  exact hzero.of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) n).app
      (Algebra.cotangentComplex A B)).symm

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
  by
    have _hST := hST
    letI : IsIso (tensorMap A B Bₜ) :=
      ((transitivityTriangle A B Bₜ).isZero₃_iff_isIso₁
        (transitivityTriangle_distinguished A B Bₜ)).mp
        (isZero_derived_of_isLocalization B Bₜ T)
    letI : IsIso (tensorComparison A Aₛ Bₜ) := tensorComparison_isIso A Aₛ Bₜ
    have hzero : IsZero (tensor A Aₛ Bₜ) :=
      IsZero.of_epi (tensorComparison A Aₛ Bₜ)
        ((ModuleCat.derivedExtensionOfScalars (algebraMap Aₛ Bₜ)).map_isZero
          (isZero_derived_of_isLocalization A Aₛ S))
    letI : IsIso (toRelativeMap A Aₛ Bₜ) :=
      ((transitivityTriangle A Aₛ Bₜ).isZero₁_iff_isIso₂
        (transitivityTriangle_distinguished A Aₛ Bₜ)).mp hzero
    infer_instance

/-- Under localization of `A` at `S` and of `B` at `T` with `S` mapping into `T`,
the objects `derived Aₛ Bₜ` and `tensor A B Bₜ` are isomorphic in `D(Bₜ)`. -/
theorem isIsomorphic_derived_tensor_of_isLocalization (A B Aₛ Bₜ : Type u)
    [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₜ]
    [Algebra A B] [Algebra A Aₛ] [Algebra B Bₜ] [Algebra Aₛ Bₜ] [Algebra A Bₜ]
    [IsScalarTower A B Bₜ] [IsScalarTower A Aₛ Bₜ]
    (S : Submonoid A) (T : Submonoid B) [IsLocalization S Aₛ] [IsLocalization T Bₜ]
    (hST : S ≤ T.comap (algebraMap A B)) :
    IsIsomorphic (derived Aₛ Bₜ) (tensor A B Bₜ) := by
  letI := tensorMap_comp_toRelativeMap_isIso A B Aₛ Bₜ S T hST
  exact ⟨(asIso (tensorMap A B Bₜ ≫ toRelativeMap A Aₛ Bₜ)).symm⟩

end Algebra.CotangentComplex
