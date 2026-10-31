/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Rank.Domain
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Tactic.CrossRefAttribute
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Grothendieck Rank over a Principal Ideal Domain

Over a principal ideal domain, every finite-module Grothendieck class is its
generic rank times `[R]`. This supplies explicit inverse maps and identifies
both `K₀(R)` and `K'_0(R)` with `ℤ`.

@stack 0FJ8
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat.K0

-- Split off one coordinate to compute the class of a standard finite free module.
private theorem pid_class_pi (R : Type u) [CommRing R]
    (P : ObjectProperty (ModuleCat.{u} R))
    (hR : P (ModuleCat.of R R))
    (hPi : ∀ n : ℕ, P (ModuleCat.of R (Fin n → R))) (n : ℕ) :
    ObjectProperty.GrothendieckGroup.of P ⟨ModuleCat.of R (Fin n → R), hPi n⟩ =
      n • ObjectProperty.GrothendieckGroup.of P ⟨ModuleCat.of R R, hR⟩ := by
  induction n with
  | zero =>
      simpa using of_subsingleton R
        (⟨ModuleCat.of R (Fin 0 → R), hPi 0⟩ : P.FullSubcategory)
  | succ n ih =>
      let f : R →ₗ[R] (Fin (n + 1) → R) :=
        (LinearMap.id : R →ₗ[R] R).vecCons 0
      let g : (Fin (n + 1) → R) →ₗ[R] (Fin n → R) :=
        LinearMap.pi fun i ↦ LinearMap.proj i.succ
      let S : ShortComplex P.FullSubcategory :=
        { X₁ := ⟨ModuleCat.of R R, hR⟩
          X₂ := ⟨ModuleCat.of R (Fin (n + 1) → R), hPi (n + 1)⟩
          X₃ := ⟨ModuleCat.of R (Fin n → R), hPi n⟩
          f := ObjectProperty.homMk (ModuleCat.ofHom f)
          g := ObjectProperty.homMk (ModuleCat.ofHom g)
          zero := by
            apply ObjectProperty.hom_ext
            apply ModuleCat.hom_ext
            rfl }
      have hS : (S.map P.ι).ShortExact := by
        apply ModuleCat.shortComplex_shortExact
        · intro x
          change (fun i : Fin n ↦ x i.succ) = 0 ↔ ∃ r, Fin.cons r 0 = x
          constructor
          · intro hx
            refine ⟨x 0, ?_⟩
            funext i
            refine Fin.cases rfl (fun j ↦ ?_) i
            exact (congrFun hx j).symm
          · rintro ⟨r, rfl⟩
            rfl
        · intro r s h
          exact congrFun h 0
        · intro x
          exact ⟨Fin.cons 0 x, rfl⟩
      calc
        _ = ObjectProperty.GrothendieckGroup.of P S.X₁ +
            ObjectProperty.GrothendieckGroup.of P S.X₃ :=
          ObjectProperty.GrothendieckGroup.of_shortExact S hS
        _ = _ := by
          change _ + ObjectProperty.GrothendieckGroup.of P
            ⟨ModuleCat.of R (Fin n → R), hPi n⟩ = _
          rw [ih, succ_nsmul, add_comm]

-- A finite basis transports the standard calculation to any finite free module.
private theorem pid_class_free (R : Type u) [CommRing R] [IsDomain R]
    (P : ObjectProperty (ModuleCat.{u} R))
    (h0 : P (ModuleCat.of R PUnit)) (hR : P (ModuleCat.of R R))
    (hPi : ∀ n : ℕ, P (ModuleCat.of R (Fin n → R)))
    (M : P.FullSubcategory) [Module.Finite R M.obj] [Module.Free R M.obj] :
    ObjectProperty.GrothendieckGroup.of P M =
      Module.finrank R M.obj •
        ObjectProperty.GrothendieckGroup.of P ⟨ModuleCat.of R R, hR⟩ := by
  let e : M ≅ ⟨ModuleCat.of R (Fin (Module.finrank R M.obj) → R), hPi _⟩ :=
    P.isoMk (Module.finBasis R M.obj).equivFun.toModuleIso
  exact (of_iso R h0 e).trans (pid_class_pi R P hR hPi _)

end CategoryTheory.ModuleCat.K0

namespace CategoryTheory.ModuleCat.K0.Finite

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- Over a PID, the virtual free class of the generic rank of a finite-module
Grothendieck class is the original class. -/
@[simp, stacks 0FJ8 "finite-module classes are determined by generic rank"]
theorem free_genericRank (x : finite.{u, u} R) :
    free R (genericRank.{u, u} R x) = x := by
  have hfree (N : Type u) [AddCommGroup N] [Module R N]
      [Module.Finite R N] [Module.Free R N] :
      finiteClass R N = free R (Module.finrank R N : ℤ) := by
    change _ = (Module.finrank R N : ℤ) • rankOne R
    simpa only [rankOne, natCast_zsmul] using
      pid_class_free R (ModuleCat.isFG R) (inferInstanceAs (Module.Finite R PUnit))
        (inferInstanceAs (Module.Finite R R))
        (fun n ↦ inferInstanceAs (Module.Finite R (Fin n → R))) (FGModuleCat.of R N)
  suffices h : (free R).comp (genericRank R) = AddMonoidHom.id _ from
    DFunLike.congr_fun h x
  ext M
  -- The kernel of a finite free presentation over a PID is finite free as well.
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M.obj
  let S : ShortComplex (FGModuleCat.{u} R) :=
    { X₁ := FGModuleCat.of R (LinearMap.ker f)
      X₂ := FGModuleCat.of R (Fin n → R)
      X₃ := M
      f := ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.ker f).subtype)
      g := ObjectProperty.homMk (ModuleCat.ofHom f)
      zero := by
        apply ObjectProperty.hom_ext
        apply ModuleCat.hom_ext
        exact LinearMap.comp_ker_subtype f }
  have hS : (S.map (ModuleCat.isFG R).ι).ShortExact :=
    LinearMap.shortExact_shortComplexKer hf
  have hrel := ObjectProperty.GrothendieckGroup.of_shortExact S hS
  change finiteClass R (Fin n → R) = finiteClass R (LinearMap.ker f) + finiteOf R M at hrel
  rw [hfree (Fin n → R), hfree (LinearMap.ker f)] at hrel
  have hM : finiteOf R M =
      free R ((Module.finrank R (Fin n → R) : ℤ) -
        (Module.finrank R (LinearMap.ker f) : ℤ)) := by
    rw [map_sub, eq_sub_iff_add_eq, add_comm]
    exact hrel.symm
  change free R (genericRank R (finiteOf R M)) = finiteOf R M
  rw [hM, genericRank_free]

/-- Generic rank identifies the finite-module Grothendieck group of a PID with
`ℤ`; the inverse is explicitly the virtual free-class map. -/
@[stacks 0FJ8 "finite-module K0 of a PID"]
def genericRankEquiv : finite.{u, u} R ≃+ ℤ where
  toFun := genericRank R
  invFun := free R
  left_inv := free_genericRank R
  right_inv := genericRank_free R
  map_add' := (genericRank R).map_add

/-- The finite-module generic-rank equivalence acts by `genericRank`. -/
@[simp]
theorem genericRankEquiv_apply (x : finite.{u, u} R) :
    genericRankEquiv R x = genericRank R x := rfl

/-- The inverse finite-module generic-rank equivalence is `free`. -/
@[simp]
theorem genericRankEquiv_symm_apply (n : ℤ) :
    (genericRankEquiv R).symm n = free R n := rfl

/-- The generic-rank homomorphism on finite modules is bijective over a PID. -/
@[stacks 0FJ8 "bijectivity of finite-module generic rank"]
theorem genericRank_bijective :
    Function.Bijective (genericRank.{u, u} R) :=
  (genericRankEquiv R).bijective

end CategoryTheory.ModuleCat.K0.Finite

namespace CategoryTheory.ModuleCat.K0.Projective

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- Over a PID, the virtual free class of projective generic rank is the
original projective Grothendieck class. -/
@[simp, stacks 0FJ8 "projective classes are determined by generic rank"]
theorem free_genericRank (x : projective.{u, u} R) :
    free R (genericRank.{u, u} R x) = x := by
  suffices h : (free R).comp (genericRank R) = AddMonoidHom.id _ from
    DFunLike.congr_fun h x
  ext M
  -- Embed the projective summand in a finite free module to obtain torsion-freeness.
  obtain ⟨n, _, g, _, hg, _⟩ := Module.Finite.exists_comp_eq_id_of_projective R M.obj
  letI : Module.IsTorsionFree R M.obj := hg.moduleIsTorsionFree g (map_smul g)
  letI : Module.Free R M.obj := inferInstance
  change free R (genericRank R (projectiveOf R M)) = projectiveOf R M
  rw [genericRank_of]
  change (Module.finrank R M.obj : ℤ) • rankOne R = _
  symm
  simpa only [rankOne, natCast_zsmul] using
    pid_class_free R (ModuleCat.finiteProjective R) (by exact ⟨inferInstance, inferInstance⟩)
      (by exact ⟨inferInstance, inferInstance⟩)
      (fun _ ↦ by exact ⟨inferInstance, inferInstance⟩) M

/-- Projective generic rank identifies `K₀(R)` of a PID with `ℤ`; its inverse
is explicitly the virtual free-projective-class map. -/
@[stacks 0FJ8 "projective K0 of a PID"]
def genericRankEquiv : projective.{u, u} R ≃+ ℤ where
  toFun := genericRank R
  invFun := free R
  left_inv := free_genericRank R
  right_inv := genericRank_free R
  map_add' := (genericRank R).map_add

/-- The projective generic-rank equivalence acts by `genericRank`. -/
@[simp]
theorem genericRankEquiv_apply (x : projective.{u, u} R) :
    genericRankEquiv R x = genericRank R x := rfl

/-- The inverse projective generic-rank equivalence is `free`. -/
@[simp]
theorem genericRankEquiv_symm_apply (n : ℤ) :
    (genericRankEquiv R).symm n = free R n := rfl

/-- The projective generic-rank homomorphism is bijective over a PID. -/
@[stacks 0FJ8 "bijectivity of projective generic rank"]
theorem genericRank_bijective :
    Function.Bijective (genericRank.{u, u} R) :=
  (genericRankEquiv R).bijective

end CategoryTheory.ModuleCat.K0.Projective

namespace CategoryTheory.ModuleCat.K0

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- Under the two generic-rank equivalences, `projectiveToFinite` acts as the
identity on `ℤ`. -/
@[simp, stacks 0FJ8 "projective-to-finite comparison in generic-rank coordinates"]
theorem genericRankEquiv_projectiveToFinite_apply (x : projective.{u, u} R) :
    Finite.genericRankEquiv R (projectiveToFinite R x) =
      Projective.genericRankEquiv R x := rfl

/-- The projective-to-finite comparison over a PID is the identification
obtained by passing through the two explicit generic-rank equivalences. -/
@[stacks 0FJ8 "projective-to-finite comparison over a PID"]
theorem projectiveToFinite_eq_viaGenericRank :
    projectiveToFinite.{u, u} R =
      (Finite.genericRankEquiv R).symm.toAddMonoidHom.comp
        (Projective.genericRankEquiv R).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  exact (Finite.free_genericRank R (projectiveToFinite R x)).symm

end CategoryTheory.ModuleCat.K0
