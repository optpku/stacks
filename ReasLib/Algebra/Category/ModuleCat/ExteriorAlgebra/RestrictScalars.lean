/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.ExteriorAlgebra

/-!
# Exterior algebras and restriction of scalars

This file bundles the exterior-algebra map induced by a morphism whose target is a module over a
different commutative ring.  Scalar restriction remains visible in the target, so presheaf
restriction maps do not replace ambient module instances.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace ModuleCat.exteriorAlgebra

variable {R S T : Type u}
variable [CommRing R] [CommRing S] [CommRing T]

/-- The semilinear degree-one exterior generator after a module morphism into a restriction of
scalars. -/
noncomputable def ιRestrictScalars (φ : R →+* S)
    {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) :
    M →ₛₗ[φ] ExteriorAlgebra S N where
  toFun x := ExteriorAlgebra.ι S (f x)
  map_add' := sorry
  map_smul' := sorry

/-- The scalar-restricted degree-one generator has square zero in the target exterior algebra. -/
theorem ιRestrictScalars_sq_zero (φ : R →+* S)
    {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (x : M) :
    ιRestrictScalars φ f x * ιRestrictScalars φ f x = 0 := sorry

/-- The ring homomorphism on exterior algebras induced along a scalar restriction.

The implementation-local `Algebra R (ExteriorAlgebra S N)` supplies precisely the scalar action
required by the universal property and is not exported to instance search. -/
noncomputable def mapRestrictScalarsRingHom (φ : R →+* S)
    {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) :
    ExteriorAlgebra R M →+* ExteriorAlgebra S N :=
  -- Local instance justification (defeq pin): `ExteriorAlgebra.lift` requires the composite
  -- `R`-algebra structure, which remains confined to this scalar-change implementation.
  letI : Algebra R (ExteriorAlgebra S N) :=
    Algebra.compHom (ExteriorAlgebra S N) φ
  (ExteriorAlgebra.lift R
    ⟨{ toFun := ιRestrictScalars φ f
       map_add' := sorry
       map_smul' := sorry },
      ιRestrictScalars_sq_zero φ f⟩).toRingHom

/-- The scalar-restricted exterior-algebra ring homomorphism agrees with `φ` on scalars. -/
@[simp]
theorem mapRestrictScalarsRingHom_algebraMap (φ : R →+* S)
    {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (r : R) :
    mapRestrictScalarsRingHom φ f (algebraMap R (ExteriorAlgebra R M) r) =
      algebraMap S (ExteriorAlgebra S N) (φ r) := sorry

/-- The scalar-restricted exterior-algebra ring homomorphism is semilinear over `φ`. -/
theorem mapRestrictScalarsRingHom_smul (φ : R →+* S)
    {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (r : R)
    (x : ExteriorAlgebra R M) :
    mapRestrictScalarsRingHom φ f (r • x) =
      φ r • mapRestrictScalarsRingHom φ f x := sorry

/-- The exterior-algebra map induced by a morphism into a restriction of scalars. -/
noncomputable def mapRestrictScalars (φ : R →+* S)
    {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) :
    M.exteriorAlgebra ⟶ (ModuleCat.restrictScalars φ).obj N.exteriorAlgebra :=
  ModuleCat.semilinearMapAddEquiv φ M.exteriorAlgebra N.exteriorAlgebra
    { toFun := mapRestrictScalarsRingHom φ f
      map_add' := (mapRestrictScalarsRingHom φ f).map_add
      map_smul' := mapRestrictScalarsRingHom_smul φ f }

/-- A scalar-restricted exterior-algebra map sends a degree-one generator to the generator of
its image. -/
@[simp]
theorem mapRestrictScalars_ι (φ : R →+* S)
    {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (x : M) :
    mapRestrictScalars φ f (ι M x) = ι N (f x) := sorry

/-- Exterior algebras carry an identity scalar-restriction morphism to the corresponding
identity scalar-restriction morphism. -/
theorem mapRestrictScalars_id (φ : R →+* R) (hφ : φ = RingHom.id R)
    (M : ModuleCat.{v} R) :
    mapRestrictScalars φ (ModuleCat.restrictScalarsId'App φ hφ M).inv =
      (ModuleCat.restrictScalarsId'App φ hφ M.exteriorAlgebra).inv := sorry

/-- Exterior algebras preserve composition over composable scalar maps, including the canonical
comparison between iterated and composite scalar restriction. -/
theorem mapRestrictScalars_comp (φ : R →+* S) (ψ : S →+* T) (χ : R →+* T)
    (hχ : χ = ψ.comp φ) {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    {P : ModuleCat.{v} T}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N)
    (g : N ⟶ (ModuleCat.restrictScalars ψ).obj P) :
    mapRestrictScalars χ
        (f ≫ (ModuleCat.restrictScalars φ).map g ≫
          (ModuleCat.restrictScalarsComp' φ ψ χ hχ).inv.app P) =
      mapRestrictScalars φ f ≫
        (ModuleCat.restrictScalars φ).map (mapRestrictScalars ψ g) ≫
        (ModuleCat.restrictScalarsComp' φ ψ χ hχ).inv.app P.exteriorAlgebra := sorry

end ModuleCat.exteriorAlgebra
