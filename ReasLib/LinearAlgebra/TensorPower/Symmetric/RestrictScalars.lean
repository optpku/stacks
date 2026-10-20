module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.LinearAlgebra.TensorPower.Symmetric

@[expose] public section

open scoped TensorProduct

/-!
# Restriction of scalars for symmetric tensor powers

This file provides the symmetric-power map induced by an `R`-linear map into an `S`-module,
viewed over `R` through an algebra `R →ₐ S`.  The codomain uses mathlib's
`RestrictScalars` type alias, so consumers do not need to rebuild a competing `Module R`
instance on the raw symmetric power.
-/

namespace SymmetricPower

universe u v w x

section

variable {R S : Type u} [CommSemiring R] [CommSemiring S] [Algebra R S]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module S N] [Module R N] [IsScalarTower R S N]
-- Mathlib's raw `SymmetricPower` requires its index type to share the coefficient-ring
-- universe. A mixed-universe bridge would necessarily expose `ULift`, so this ergonomic owner
-- intentionally serves the common same-universe scalar-tower case.
variable {ι : Type u}

/-- The map on `ι`-indexed symmetric powers induced by an `R`-linear map to an `S`-module.

The target is the canonical `RestrictScalars` alias.  The scalar tower on `N` lets the
`S`-multilinear symmetric generator be regarded as `R`-multilinear. -/
noncomputable def restrictScalarsMap (f : M →ₗ[R] N) :
    Sym[R] ι M →ₗ[R] RestrictScalars R S (Sym[S] ι N) := by
  let tprodN' : MultilinearMap R (fun _ : ι ↦ N) (RestrictScalars R S (Sym[S] ι N)) := by
    -- Local instance justification (instance diamond): recover the original `S` action only
    -- while restricting the symmetric generator to scalars in `R`.
    letI : Module S (RestrictScalars R S (Sym[S] ι N)) :=
      RestrictScalars.moduleOrig R S (Sym[S] ι N)
    let tprodN : MultilinearMap S (fun _ : ι ↦ N)
        (RestrictScalars R S (Sym[S] ι N)) := SymmetricPower.tprod S
    exact tprodN.restrictScalars R
  let tensorLift : (⨂[R] (_ : ι), M) →ₗ[R] RestrictScalars R S (Sym[S] ι N) :=
    PiTensorProduct.lift (tprodN'.compLinearMap fun _ ↦ f)
  have hrel :
      addConGen (SymmetricPower.Rel R ι M) ≤ AddCon.ker tensorLift.toAddMonoidHom := by
    intro x y h
    induction h with
    | of _ _ hrel =>
        cases hrel with
        | perm e m =>
            change tensorLift (PiTensorProduct.tprod R (fun i ↦ m i)) =
              tensorLift (PiTensorProduct.tprod R (fun i ↦ m (e i)))
            simp only [tensorLift, PiTensorProduct.lift.tprod]
            exact (SymmetricPower.tprod_equiv e (f ∘ m)).symm
    | refl => rfl
    | symm hxy ih => exact ih.symm
    | trans hxy hyz ihxy ihyz => exact ihxy.trans ihyz
    | add hxy hyz ihxy ihyz => simpa using congrArg₂ (· + ·) ihxy ihyz
  let liftHom : Sym[R] ι M →+ RestrictScalars R S (Sym[S] ι N) :=
    AddCon.lift _ tensorLift.toAddMonoidHom hrel
  exact
    { toFun := liftHom
      map_add' := liftHom.map_add
      map_smul' := by
        intro r q
        refine AddCon.induction_on q ?_
        intro x
        change tensorLift (r • x) = r • tensorLift x
        exact tensorLift.map_smul r x }

/-- `restrictScalarsMap` sends a pure symmetric tensor to the symmetric tensor of its
entrywise image. -/
@[simp] theorem restrictScalarsMap_tprod (f : M →ₗ[R] N) (m : ι → M) :
    restrictScalarsMap (R := R) (S := S) f (SymmetricPower.tprod R m) =
      (SymmetricPower.tprod S (f ∘ m) : RestrictScalars R S (Sym[S] ι N)) := sorry

end

end SymmetricPower
