module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.SymmetricAlgebra

/-!
# Symmetric algebras and restriction of scalars

This file constructs the symmetric-algebra map induced by a morphism into a restriction of
scalars.  The varying scalar action is confined to this constructor; consumers receive an
ordinary bundled morphism in `ModuleCat`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace ModuleCat.symmetricAlgebra

variable {R S T : Type u}
variable [CommRing R] [CommRing S] [CommRing T]

/-- The multiplicative symmetric-algebra map along a scalar restriction.

The target acquires its `R`-algebra structure by composing its canonical `S`-algebra structure
with `φ`; this action depends on the chosen ring morphism and is therefore kept out of global
instance search. -/
noncomputable def mapRestrictScalarsRingHom (φ : R →+* S)
    {M : ModuleCat R} {N : ModuleCat S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) :
    SymmetricAlgebra R M →+* SymmetricAlgebra S N :=
  -- Local instance justification (instance diamond): the target `R`-algebra action depends on
  -- the explicit scalar map `φ`, so registering it globally would create competing actions.
  letI : Algebra R (SymmetricAlgebra S N) := Algebra.compHom _ φ
  (SymmetricAlgebra.lift
    (f ≫ (ModuleCat.restrictScalars φ).map (ModuleCat.ofHom (ι N))).hom).toRingHom

/-- The multiplicative symmetric-algebra map along scalar restriction preserves addition. -/
theorem mapRestrictScalarsRingHom_add (φ : R →+* S)
    {M : ModuleCat R} {N : ModuleCat S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (x y : M.symmetricAlgebra) :
    mapRestrictScalarsRingHom φ f (x + y) =
      mapRestrictScalarsRingHom φ f x + mapRestrictScalarsRingHom φ f y := sorry

/-- The multiplicative symmetric-algebra map along scalar restriction is `φ`-semilinear. -/
theorem mapRestrictScalarsRingHom_smul (φ : R →+* S)
    {M : ModuleCat R} {N : ModuleCat S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (r : R) (x : M.symmetricAlgebra) :
    mapRestrictScalarsRingHom φ f (r • x) =
      φ r • mapRestrictScalarsRingHom φ f x := sorry

/-- The symmetric-algebra map induced by a morphism into a restriction of scalars. -/
noncomputable def mapRestrictScalars (φ : R →+* S)
    {M : ModuleCat R} {N : ModuleCat S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) :
    M.symmetricAlgebra ⟶ (ModuleCat.restrictScalars φ).obj N.symmetricAlgebra :=
  ModuleCat.semilinearMapAddEquiv φ M.symmetricAlgebra N.symmetricAlgebra
    { toFun := mapRestrictScalarsRingHom φ f
      map_add' := mapRestrictScalarsRingHom_add φ f
      map_smul' := mapRestrictScalarsRingHom_smul φ f }

/-- `mapRestrictScalars` sends a symmetric-algebra generator to the generator of its image. -/
@[simp]
theorem mapRestrictScalars_ι (φ : R →+* S)
    {M : ModuleCat R} {N : ModuleCat S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (x : M) :
    mapRestrictScalars φ f (ι M x) = ι N (f x) := sorry

/-- Symmetric algebras carry an identity scalar-restriction morphism to the corresponding
identity scalar-restriction morphism. -/
theorem mapRestrictScalars_id (φ : R →+* R) (hφ : φ = RingHom.id R)
    (M : ModuleCat R) :
    mapRestrictScalars φ (ModuleCat.restrictScalarsId'App φ hφ M).inv =
      (ModuleCat.restrictScalarsId'App φ hφ M.symmetricAlgebra).inv := sorry

/-- Symmetric algebras preserve composition over composable scalar maps, including the canonical
comparison between iterated and composite scalar restriction. -/
theorem mapRestrictScalars_comp (φ : R →+* S) (ψ : S →+* T) (χ : R →+* T)
    (hχ : χ = ψ.comp φ) {M : ModuleCat R} {N : ModuleCat S} {P : ModuleCat T}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N)
    (g : N ⟶ (ModuleCat.restrictScalars ψ).obj P) :
    mapRestrictScalars χ
        (f ≫ (ModuleCat.restrictScalars φ).map g ≫
          (ModuleCat.restrictScalarsComp' φ ψ χ hχ).inv.app P) =
      mapRestrictScalars φ f ≫
        (ModuleCat.restrictScalars φ).map (mapRestrictScalars ψ g) ≫
        (ModuleCat.restrictScalarsComp' φ ψ χ hχ).inv.app P.symmetricAlgebra := sorry

end ModuleCat.symmetricAlgebra
