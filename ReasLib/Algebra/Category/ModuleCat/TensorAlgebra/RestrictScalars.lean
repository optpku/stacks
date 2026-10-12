/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.TensorAlgebra

/-!
# Tensor algebras and restriction of scalars

This file bundles the tensor-algebra map induced by a morphism whose target is a module over a
different commutative ring.  The public module morphism lands in Mathlib's bundled
`ModuleCat.restrictScalars`, so no competing scalar action is exposed to downstream users.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace ModuleCat.tensorAlgebra

variable {R S T : Type u}
variable [CommRing R] [CommRing S] [CommRing T]

/-- The multiplicative tensor-algebra map along a scalar restriction.

The local instances in the implementation are forced by `TensorAlgebra.lift`: its target must
temporarily be viewed as an `R`-algebra and `N` as an `R`-module in the scalar tower
`R → S → N`.  They are definitionally the actions owned by `φ` and do not occur in the public
type. -/
noncomputable def mapRestrictScalarsRingHom (φ : R →+* S)
    {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) :
    TensorAlgebra R M →+* TensorAlgebra S N :=
  -- Local instance justification (defeq pin): expose the `R`-algebra selected by `φ` to `lift`.
  letI : Algebra R S := φ.toAlgebra
  -- Local instance justification (defeq pin): use the scalar action bundled by `restrictScalars φ`.
  letI : Module R N := Module.compHom N φ
  -- Local instance justification (defeq pin): connect the preceding two canonical scalar actions.
  letI : IsScalarTower R S N :=
    @IsScalarTower.of_compHom R S N _ _ φ.toAlgebra _
  (TensorAlgebra.lift R
    (((TensorAlgebra.ι S : N →ₗ[S] TensorAlgebra S N).restrictScalars R).comp f.hom)).toRingHom

/-- The tensor-algebra map along scalar restriction sends a degree-one generator to the image
generator. -/
theorem mapRestrictScalarsRingHom_ι (φ : R →+* S)
    {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (m : M) :
    mapRestrictScalarsRingHom φ f (TensorAlgebra.ι R m) =
      TensorAlgebra.ι S (f m) := sorry

/-- The tensor-algebra ring homomorphism along scalar restriction agrees with `φ` on base
scalars. -/
@[simp]
theorem mapRestrictScalarsRingHom_algebraMap (φ : R →+* S)
    {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (r : R) :
    mapRestrictScalarsRingHom φ f (algebraMap R (TensorAlgebra R M) r) =
      algebraMap S (TensorAlgebra S N) (φ r) := sorry

/-- The underlying tensor-algebra function along a scalar restriction preserves addition. -/
theorem mapRestrictScalars_add (φ : R →+* S)
    {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (x y : M.tensorAlgebra) :
    mapRestrictScalarsRingHom φ f (x + y) =
      mapRestrictScalarsRingHom φ f x + mapRestrictScalarsRingHom φ f y := sorry

/-- The underlying tensor-algebra function along a scalar restriction is semilinear over the
ring morphism. -/
theorem mapRestrictScalars_smul (φ : R →+* S)
    {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (r : R) (x : M.tensorAlgebra) :
    mapRestrictScalarsRingHom φ f (r • x) =
      φ r • mapRestrictScalarsRingHom φ f x := sorry

/-- The bundled morphism on tensor algebras induced by a morphism into a restriction of
scalars. -/
noncomputable def mapRestrictScalars (φ : R →+* S)
    {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) :
    M.tensorAlgebra ⟶ (ModuleCat.restrictScalars φ).obj N.tensorAlgebra :=
  ModuleCat.semilinearMapAddEquiv φ M.tensorAlgebra N.tensorAlgebra
    { toFun := mapRestrictScalarsRingHom φ f
      map_add' := mapRestrictScalars_add φ f
      map_smul' := mapRestrictScalars_smul φ f }

/-- The bundled tensor-algebra map along scalar restriction acts on a degree-one generator by
the original module morphism. -/
@[simp]
theorem mapRestrictScalars_ι (φ : R →+* S)
    {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (m : M) :
    mapRestrictScalars φ f (ι M m) = ι N (f m) := sorry

/-- Tensor-algebra restriction maps over an identity scalar morphism agree with the canonical
identity-restriction comparison. -/
theorem mapRestrictScalars_id (φ : R →+* R) (hφ : φ = RingHom.id R)
    (M : ModuleCat.{v} R) :
    mapRestrictScalars φ (ModuleCat.restrictScalarsId'App φ hφ M).inv =
      (ModuleCat.restrictScalarsId'App φ hφ M.tensorAlgebra).inv := sorry

/-- Tensor-algebra maps preserve composition over composable scalar morphisms, including the
canonical comparison between iterated and composite restriction of scalars. -/
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
        (ModuleCat.restrictScalarsComp' φ ψ χ hχ).inv.app P.tensorAlgebra := sorry

end ModuleCat.tensorAlgebra
