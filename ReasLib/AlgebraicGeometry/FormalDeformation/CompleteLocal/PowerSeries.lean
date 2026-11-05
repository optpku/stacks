/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalHomotopy
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Instances
public import ReasLib.AlgebraicGeometry.FormalDeformation.TypesCompletion
public import ReasLib.RingTheory.LocalRing.IdealQuotient
public import ReasLib.RingTheory.PowerSeriesExtension
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Order.Disjoint

/-!
# Power series morphisms in `CompleteLocalAlgCat`

A morphism `f : R ⟶ S` exhibits `S` as a finite-variable power series ring over `R`
when, after an isomorphism of complete local algebras, it becomes the canonical
coefficient inclusion `R.mvPowerSeriesC n`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- A morphism `f : R ⟶ S` exhibits `S` as a power series ring over `R` if there is
`n : ℕ` and an isomorphism `e : S ≅ R.mvPowerSeries n` with
`f ≫ e.hom = R.mvPowerSeriesC n`. -/
def IsPowerSeriesOver {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) : Prop :=
  ∃ n : ℕ, ∃ e : S ≅ R.mvPowerSeries n, f ≫ e.hom = R.mvPowerSeriesC n

/-- Being a power series over `R` unpacks to a finite-variable isomorphism over the
canonical coefficient inclusion. -/
theorem isPowerSeriesOver_iff {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    IsPowerSeriesOver f ↔
      ∃ n : ℕ, ∃ e : S ≅ R.mvPowerSeries n, f ≫ e.hom = R.mvPowerSeriesC n :=
  Iff.rfl

/-- An isomorphism onto `R.mvPowerSeries n` over `R.mvPowerSeriesC n` exhibits a
power series morphism. -/
theorem IsPowerSeriesOver.of_iso {R S : CompleteLocalAlgCat Λ k} {n : ℕ} {f : R ⟶ S}
    (e : S ≅ R.mvPowerSeries n) (h : f ≫ e.hom = R.mvPowerSeriesC n) :
    IsPowerSeriesOver f :=
  ⟨n, e, h⟩

/-- The canonical coefficient inclusion `R.mvPowerSeriesC n` is a power series
morphism over `R`. -/
theorem isPowerSeriesOver_mvPowerSeriesC (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    IsPowerSeriesOver (R.mvPowerSeriesC n) :=
  ⟨n, Iso.refl _, Category.comp_id _⟩

/-- Morphisms with the same algebra map are equal, including their proof fields. -/
theorem Hom.ext {source target : CompleteLocalAlgCat Λ k} {first second : source ⟶ target}
    (equalMaps : first.hom = second.hom) : first = second := by
  rcases first with ⟨first, firstLocal, firstResidue⟩
  rcases second with ⟨second, secondLocal, secondResidue⟩
  cases equalMaps
  rfl

/-- Forget a marked isomorphism using its supplied forward and inverse maps. -/
def isoRingEquiv {source target : CompleteLocalAlgCat Λ k} (iso : source ≅ target) :
    source.carrier ≃+* target.carrier where
  __ := iso.hom.toRingHom
  invFun := iso.inv.hom
  left_inv value := congrArg (fun map : source ⟶ source => map.hom value) iso.hom_inv_id
  right_inv value := congrArg (fun map : target ⟶ target => map.hom value) iso.inv_hom_id

/-- Forgetting a marked isomorphism preserves its forward ring map. -/
theorem isoRingEquiv_toRingHom {source target : CompleteLocalAlgCat Λ k}
    (iso : source ≅ target) : (isoRingEquiv iso).toRingHom = iso.hom.toRingHom := rfl

/-- Lift an explicit ring isomorphism over a marked coefficient map. Its scalar
action is forced by `map`; the residue identifications are those stored in the
source, target and canonical power-series object. Both maps are supplied by `equiv`. -/
noncomputable def powerSeriesIsoOfRingEquiv {source target : CompleteLocalAlgCat Λ k}
    (map : source ⟶ target) (numVars : ℕ)
    (equiv : target.carrier ≃+* MvPowerSeries (Fin numVars) source.carrier)
    (compat : equiv.toRingHom.comp map.toRingHom = MvPowerSeries.C) :
    target ≅ source.mvPowerSeries numVars := by
  let algEquiv : target.carrier ≃ₐ[Λ] (source.mvPowerSeries numVars).carrier :=
    AlgEquiv.ofRingEquiv (f := equiv) (by
      intro scalar
      calc
        equiv (algebraMap Λ target.carrier scalar) =
            equiv (map.hom (algebraMap Λ source.carrier scalar)) := by rw [map.hom.commutes]
        _ = MvPowerSeries.C (algebraMap Λ source.carrier scalar) :=
          DFunLike.congr_fun compat _
        _ = algebraMap Λ (source.mvPowerSeries numVars).carrier scalar :=
          MvPowerSeries.algebraMap_apply.symm)
  exact
    { hom := Hom.of (A := target) (B := source.mvPowerSeries numVars)
        algEquiv.toAlgHom inferInstance (by sorry)
      inv := Hom.of (A := source.mvPowerSeries numVars) (B := target)
        algEquiv.symm.toAlgHom inferInstance (by sorry)
      hom_inv_id := by
        apply Hom.ext
        apply AlgHom.ext
        intro value
        exact algEquiv.left_inv value
      inv_hom_id := by
        apply Hom.ext
        apply AlgHom.ext
        intro value
        exact algEquiv.right_inv value }

/-- The marked lift uses the original forward ring map. -/
theorem powerSeriesIsoOfRingEquiv_hom {source target : CompleteLocalAlgCat Λ k}
    (map : source ⟶ target) (numVars : ℕ)
    (equiv : target.carrier ≃+* MvPowerSeries (Fin numVars) source.carrier)
    (compat : equiv.toRingHom.comp map.toRingHom = MvPowerSeries.C) :
    (powerSeriesIsoOfRingEquiv map numVars equiv compat).hom.toRingHom = equiv.toRingHom := rfl

/-- The marked lift uses the original inverse ring map. -/
theorem powerSeriesIsoOfRingEquiv_inv {source target : CompleteLocalAlgCat Λ k}
    (map : source ⟶ target) (numVars : ℕ)
    (equiv : target.carrier ≃+* MvPowerSeries (Fin numVars) source.carrier)
    (compat : equiv.toRingHom.comp map.toRingHom = MvPowerSeries.C) :
    (powerSeriesIsoOfRingEquiv map numVars equiv compat).inv.toRingHom = equiv.symm.toRingHom := rfl

/-- For a morphism already preserving the chosen scalars and residue field, the
underlying coefficient-inclusion property lifts to the marked category. -/
theorem isPowerSeriesOver_iff_toRingHom {source target : CompleteLocalAlgCat Λ k}
    (map : source ⟶ target) :
    IsPowerSeriesOver map ↔ RingHom.IsPowerSeriesExtension map.toRingHom := by
  constructor
  · rintro ⟨numVars, iso, compat⟩
    exact ⟨numVars, isoRingEquiv iso,
      congrArg (fun other : source ⟶ source.mvPowerSeries numVars => other.toRingHom) compat⟩
  · rintro ⟨numVars, equiv, compat⟩
    refine ⟨numVars, powerSeriesIsoOfRingEquiv map numVars equiv compat, ?_⟩
    apply Hom.ext
    apply AlgHom.ext
    intro value
    exact DFunLike.congr_fun compat value

/-- `I ⧸ m_R I` is a `k`-vector space via the residue identification of `R`. -/
noncomputable instance instModule_idealSmulQuot {R : CompleteLocalAlgCat Λ k}
    {I : Ideal R.carrier} : Module k (idealSmulQuot I) :=
  Module.compHom (idealSmulQuot I) R.residueFieldIso.symm.toRingHom

/-- A power series evaluation over a split complete local algebra is bijective if its
coordinates form a residue-field basis of `I / m_R I` and its sufficiently deep
maximal-adic truncations have left inverses in the Artinian-local category. -/
theorem mvPowerSeriesEval_bijective {R' R : CompleteLocalAlgCat Λ k} (ι : R' ⟶ R)
    (I : Ideal R.carrier)
    (hcompl : IsCompl (LinearMap.range ι.hom.toLinearMap) (I.restrictScalars Λ))
    {r : ℕ} (x : Fin r → I)
    (hind : LinearIndependent k (fun i ↦ idealSmulQuot.mk (x i)))
    (hspan : Submodule.span k (Set.range fun i ↦ idealSmulQuot.mk (x i)) = ⊤)
    (φ : R'.mvPowerSeries r ⟶ R) (hφ_C : R'.mvPowerSeriesC r ≫ φ = ι)
    (hφ_X : ∀ i, φ.hom (MvPowerSeries.X i) = (x i : R.carrier))
    (hleft : ∃ N, ∀ n, N ≤ n →
      ∃ g : R.truncation n ⟶ (R'.mvPowerSeries r).truncation n,
        truncationHom φ n ≫ g = 𝟙 ((R'.mvPowerSeries r).truncation n)) :
    Function.Bijective φ.hom :=
  sorry

end CompleteLocalAlgCat
