/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.PrincipalParts.RingHom
public import ReasLib.Algebra.Module.PrincipalParts.Truncation

/-!
# Truncation for principal parts attached to an explicit ring homomorphism

This file bundles the algebraic order-transition maps in `ModuleCat`.  It completes the explicit
ring-hom interface used by objectwise presheaf and sheaf constructions.

@stack 09CL
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace PrincipalParts.RingHom

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The bundled transition from principal parts of order `l` to order `k` for `k ≤ l`. -/
@[stacks 09CL "explicit ring-hom truncation"]
noncomputable def truncate (σ : R →+* S) (M : ModuleCat.{u} S) {k l : ℕ} (h : k ≤ l) :
    module σ M l ⟶ module σ M k :=
  -- Local instance justification (instance diamond): truncation specializes the typeclass-based
  -- owner to this explicit `σ`, whose induced source action cannot be registered globally.
  letI : Algebra R S := algebra σ
  letI : Module R M := sourceModule σ M
  letI : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  ModuleCat.ofHom (PrincipalParts.truncate (R := R) (S := S) (M := M) h)

/-- Bundled truncation preserves every universal class. -/
@[simp]
theorem truncate_universalClass (σ : R →+* S) (M : ModuleCat.{u} S)
    {k l : ℕ} (h : k ≤ l) (m : M) :
    (truncate σ M h).hom (universalClass σ M l m) = universalClass σ M k m := sorry

/-- Bundled truncation is surjective on underlying elements. -/
theorem truncate_surjective (σ : R →+* S) (M : ModuleCat.{u} S)
    {k l : ℕ} (h : k ≤ l) : Function.Surjective (truncate σ M h) := sorry

/-- Truncation along a reflexive order comparison is the identity. -/
@[simp]
theorem truncate_refl (σ : R →+* S) (M : ModuleCat.{u} S) (k : ℕ) :
    truncate σ M (le_refl k) = 𝟙 (module σ M k) := sorry

/-- Successive bundled truncations equal truncation along the composite comparison. -/
@[simp]
theorem truncate_trans (σ : R →+* S) (M : ModuleCat.{u} S)
    {k l n : ℕ} (hkl : k ≤ l) (hln : l ≤ n) :
    truncate σ M hln ≫ truncate σ M hkl = truncate σ M (hkl.trans hln) := sorry

/-- Bundled truncation is natural in the module argument. -/
theorem truncate_naturality (σ : R →+* S) {M N : ModuleCat.{u} S}
    {k l : ℕ} (h : k ≤ l) (f : M ⟶ N) :
    map σ l f ≫ truncate σ N h = truncate σ M h ≫ map σ k f := sorry

/-- Truncation in the order bound is a natural transformation between principal-parts
endofunctors. -/
@[stacks 09CL "explicit ring-hom truncation natural transformation"]
noncomputable def truncateNatTrans (σ : R →+* S) {k l : ℕ} (h : k ≤ l) :
    functor σ l ⟶ functor σ k where
  app M := truncate σ M h
  naturality _ _ f := truncate_naturality σ h f

end PrincipalParts.RingHom

end
