module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.SymmetricPower
public import ReasLib.LinearAlgebra.TensorPower.Symmetric.RestrictScalars

/-!
# Symmetric powers and restriction of scalars

This file bundles the symmetric-power map induced by a morphism whose target is a module over a
different commutative ring.  Scalar restriction is part of the target object, avoiding competing
ambient module instances at presheaf restriction maps.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace ModuleCat.symmetricPower

variable {R S T : Type u}
variable [CommRing R] [CommRing S] [CommRing T]

/-- The underlying function of the symmetric-power map along a scalar restriction. -/
noncomputable def mapRestrictScalarsFun (φ : R →+* S)
    {M : ModuleCat R} {N : ModuleCat S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (n : ℕ) :
    M.symmetricPower n → N.symmetricPower n :=
  @SymmetricPower.restrictScalarsMap R S _ _ φ.toAlgebra M _ _ N _ _
    (Module.compHom N φ) (@IsScalarTower.of_compHom R S N _ _ φ.toAlgebra _)
    (SymmetricPower.UFin n) f.hom

/-- The underlying symmetric-power function along scalar restriction preserves addition. -/
theorem mapRestrictScalarsFun_add (φ : R →+* S)
    {M : ModuleCat R} {N : ModuleCat S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (n : ℕ) (x y : M.symmetricPower n) :
    mapRestrictScalarsFun φ f n (x + y) =
      mapRestrictScalarsFun φ f n x + mapRestrictScalarsFun φ f n y := sorry

/-- The underlying symmetric-power function along scalar restriction preserves scalar
multiplication in the semilinear sense. -/
theorem mapRestrictScalarsFun_smul (φ : R →+* S)
    {M : ModuleCat R} {N : ModuleCat S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (n : ℕ) (r : R)
    (x : M.symmetricPower n) :
    mapRestrictScalarsFun φ f n (r • x) = φ r • mapRestrictScalarsFun φ f n x := sorry

/-- The map on degree-`n` symmetric powers induced by a morphism into a restriction of scalars. -/
noncomputable def mapRestrictScalars (φ : R →+* S) {M : ModuleCat R} {N : ModuleCat S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (n : ℕ) :
    M.symmetricPower n ⟶ (ModuleCat.restrictScalars φ).obj (N.symmetricPower n) :=
  ModuleCat.semilinearMapAddEquiv φ (M.symmetricPower n) (N.symmetricPower n)
    { toFun := mapRestrictScalarsFun φ f n
      map_add' := mapRestrictScalarsFun_add φ f n
      map_smul' := mapRestrictScalarsFun_smul φ f n }

/-- `mapRestrictScalars` sends a pure symmetric tensor to the tensor of its entrywise image. -/
@[simp]
theorem mapRestrictScalars_mk (φ : R →+* S) {M : ModuleCat R} {N : ModuleCat S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (n : ℕ)
    (m : SymmetricPower.UFin n → M) :
    mapRestrictScalars φ f n (mk m) =
      ModuleCat.symmetricPower.mk (R := S) (M := N) (fun i ↦ f (m i)) := sorry

/-- Symmetric powers carry an identity scalar-restriction morphism to the corresponding identity
scalar-restriction morphism. -/
theorem mapRestrictScalars_id (φ : R →+* R) (hφ : φ = RingHom.id R)
    (M : ModuleCat R) (n : ℕ) :
    mapRestrictScalars φ (ModuleCat.restrictScalarsId'App φ hφ M).inv n =
      (ModuleCat.restrictScalarsId'App φ hφ (M.symmetricPower n)).inv := sorry

/-- Symmetric powers preserve composition over composable scalar maps, including the canonical
comparison between iterated and composite scalar restriction. -/
theorem mapRestrictScalars_comp (φ : R →+* S) (ψ : S →+* T) (χ : R →+* T)
    (hχ : χ = ψ.comp φ) {M : ModuleCat R} {N : ModuleCat S} {P : ModuleCat T}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N)
    (g : N ⟶ (ModuleCat.restrictScalars ψ).obj P) (n : ℕ) :
    mapRestrictScalars χ
        (f ≫ (ModuleCat.restrictScalars φ).map g ≫
          (ModuleCat.restrictScalarsComp' φ ψ χ hχ).inv.app P) n =
      mapRestrictScalars φ f n ≫
        (ModuleCat.restrictScalars φ).map (mapRestrictScalars ψ g n) ≫
        (ModuleCat.restrictScalarsComp' φ ψ χ hχ).inv.app (P.symmetricPower n) := sorry

end ModuleCat.symmetricPower
