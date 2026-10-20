/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.PrincipalParts.Basic
public import ReasLib.Algebra.Module.DifferentialOperator.Restrict
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base Change for Principal Parts

This leaf owns the module-level map on principal-parts modules induced by a
commutative square of commutative rings and a linear map of modules.  The map
is defined through the representing property of principal parts, so clients do
not need to expose a particular quotient presentation.

@stack 09CP
-/

@[expose] public section

universe u

noncomputable section

namespace PrincipalParts.BaseChange

section Map

variable {A B A' B' : Type u}
variable [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
variable [Algebra A B] [Algebra A A'] [Algebra A B'] [Algebra A' B'] [Algebra B B']
variable [IsScalarTower A B B'] [IsScalarTower A A' B']

variable {M M' : Type u}
variable [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
variable [AddCommGroup M'] [Module B' M'] [Module A M'] [Module A' M'] [Module B M']
variable [IsScalarTower A' B' M'] [IsScalarTower B B' M'] [IsScalarTower A A' M']

namespace Internal

/-- The scalar tower on a target module induced by the upper side `A → A' → B'` of a
base-change square.  It is implementation infrastructure for `map`, rather than a global
instance, because the square can carry more than one scalar-action path. -/
theorem isScalarTowerToTarget
    {X : Type u} [AddCommMonoid X] [Module B' X] [Module A' X] [Module A X]
    [IsScalarTower A A' X] [IsScalarTower A' B' X] :
    IsScalarTower A B' X :=
  sorry

/-- The scalar tower on a target module induced by the lower side `A → B → B'` of a
base-change square.  It is internal infrastructure, so typeclass search is not globally altered. -/
theorem isScalarTowerToIntermediateTarget
    {X : Type u} [AddCommMonoid X] [Module B' X] [Module B X] [Module A X]
    [IsScalarTower B B' X] [IsScalarTower A B' X] :
    IsScalarTower A B X :=
  sorry

/-- The source module map, regarded as `A`-linear through the lower scalar path of the square. -/
def sourceMap (f : M →ₗ[B] M') : M →ₗ[A] M' where
  toFun := f
  map_add' := f.map_add
  map_smul' := sorry

/-- The target universal differential, regarded as an `A`-linear map through `A → A'`. -/
def targetMap (k : ℕ) :
    M' →ₗ[A] PrincipalParts.module A' B' M' k :=
  (PrincipalParts.universalDifferential (R := A') (S := B') (M := M') k).restrictScalars A

/-- The composite of the target universal differential with the source map is an order-`k`
operator over `A → B`.  Its proof factors through the generic differential-operator restriction
lemmas, rather than through a quotient presentation of principal parts. -/
theorem operatorMem (k : ℕ) (f : M →ₗ[B] M') :
    LinearMap.IsDifferentialOperatorOfOrder
      ((targetMap (A := A) (A' := A') (B' := B') (M' := M') k).comp
        (sourceMap (A := A) (B := B) f)) B k :=
  sorry

end Internal

/-- A map of modules over a commutative square induces the canonical map from
`PrincipalParts.module A B M k` to `PrincipalParts.module A' B' M' k`. -/
@[stacks 09CP]
noncomputable def map (k : ℕ) (f : M →ₗ[B] M') :
    PrincipalParts.module A B M k →ₗ[B] PrincipalParts.module A' B' M' k :=
  -- Local instance justification (instance diamond): the ambient square supplies two scalar
  -- paths from `A` through `B`, `A'`, and `B'`; these named coherence facts select the paths
  -- required by the representing construction without registering a competing global tower.
  -- Local instance justification (instance diamond): this selects the upper scalar path on `M'`.
  letI : IsScalarTower A B' M' :=
    Internal.isScalarTowerToTarget (A := A) (A' := A') (B' := B') (X := M')
  -- Local instance justification (instance diamond): this selects the lower scalar path on `M'`.
  letI : IsScalarTower A B M' :=
    Internal.isScalarTowerToIntermediateTarget (A := A) (B := B) (B' := B') (X := M')
  -- Local instance justification (instance diamond): this selects the upper scalar path on the target principal-parts module.
  letI : IsScalarTower A B' (PrincipalParts.module A' B' M' k) :=
    Internal.isScalarTowerToTarget (A := A) (A' := A') (B' := B')
      (X := PrincipalParts.module A' B' M' k)
  -- Local instance justification (instance diamond): this selects the lower scalar path on the target principal-parts module.
  letI : IsScalarTower A B (PrincipalParts.module A' B' M' k) :=
    Internal.isScalarTowerToIntermediateTarget (A := A) (B := B) (B' := B')
      (X := PrincipalParts.module A' B' M' k)
  (PrincipalParts.representingEquiv A B M k
    (PrincipalParts.module A' B' M' k)).symm
    ⟨(Internal.targetMap (A := A) (A' := A') (B' := B') (M' := M') k).comp
        (Internal.sourceMap (A := A) (B := B) f),
      Internal.operatorMem (A := A) (B := B) (A' := A') (B' := B') k f⟩

namespace Internal

/-- The underlying function of the base-change map, with its target module structure erased
from the public type.  This lets the bundled map choose the canonical restricted scalar action. -/
noncomputable def mapFun (k : ℕ) (f : M →ₗ[B] M') :
    PrincipalParts.module A B M k →
      (ModuleCat.restrictScalars (algebraMap B B')).obj
        (ModuleCat.of B' (PrincipalParts.module A' B' M' k)) :=
  fun x ↦ map (A := A) (B := B) (A' := A') (B' := B')
    (M := M) (M' := M') k f x

/-- The underlying base-change function preserves addition. -/
theorem mapFun_add (k : ℕ) (f : M →ₗ[B] M')
    (x y : PrincipalParts.module A B M k) :
    mapFun (A := A) (B := B) (A' := A') (B' := B')
        (M := M) (M' := M') k f (x + y) =
      mapFun (A := A) (B := B) (A' := A') (B' := B')
          (M := M) (M' := M') k f x +
        mapFun (A := A) (B := B) (A' := A') (B' := B')
          (M := M) (M' := M') k f y := sorry

/-- The underlying base-change function is linear for the restricted `B`-action. -/
theorem mapFun_smul (k : ℕ) (f : M →ₗ[B] M') (b : B)
    (x : PrincipalParts.module A B M k) :
    mapFun (A := A) (B := B) (A' := A') (B' := B')
        (M := M) (M' := M') k f (b • x) =
      algebraMap B B' b • mapFun (A := A) (B := B) (A' := A') (B' := B')
        (M := M) (M' := M') k f x := sorry

end Internal

/-- The base-change map as a bundled module morphism whose target scalar restriction is explicit. -/
@[stacks 09CP "bundled module map"]
noncomputable def moduleMap (k : ℕ) (f : M →ₗ[B] M') :
    ModuleCat.of B (PrincipalParts.module A B M k) ⟶
      (ModuleCat.restrictScalars (algebraMap B B')).obj
        (ModuleCat.of B' (PrincipalParts.module A' B' M' k)) :=
  ModuleCat.ofHom
    (X := ModuleCat.of B (PrincipalParts.module A B M k))
    (Y := (ModuleCat.restrictScalars (algebraMap B B')).obj
      (ModuleCat.of B' (PrincipalParts.module A' B' M' k)))
    { toFun := Internal.mapFun (A := A) (B := B) (A' := A') (B' := B')
        (M := M) (M' := M') k f
      map_add' := Internal.mapFun_add (A := A) (B := B) (A' := A') (B' := B')
        (M := M) (M' := M') k f
      map_smul' := Internal.mapFun_smul (A := A) (B := B) (A' := A') (B' := B')
        (M := M) (M' := M') k f }

/-- The bundled base-change morphism has the same underlying function as `map`. -/
@[simp]
lemma moduleMap_apply (k : ℕ) (f : M →ₗ[B] M')
    (x : PrincipalParts.module A B M k) :
    (moduleMap (A := A) (B := B) (A' := A') (B' := B')
      (M := M) (M' := M') k f).hom x =
        map (A := A) (B := B) (A' := A') (B' := B')
          (M := M) (M' := M') k f x := sorry

/-- The base-change map sends the universal class of `m` to the universal class of `f m`. -/
@[stacks 09CP, simp]
lemma map_apply_universalDifferential (k : ℕ) (f : M →ₗ[B] M') (m : M) :
    map (A := A) (B := B) (A' := A') (B' := B') (M := M) (M' := M') k f
        (PrincipalParts.universalDifferential (R := A) (S := B) (M := M) k m) =
      PrincipalParts.universalDifferential (R := A') (S := B') (M := M') k (f m) :=
  sorry

end Map

section Identity

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- Principal-parts base change along the identity square is the identity linear map. -/
@[simp]
theorem map_id (k : ℕ) :
    map (A := R) (B := R) (A' := R) (B' := R) (M := M) (M' := M) k
        (LinearMap.id : M →ₗ[R] M) = LinearMap.id :=
  sorry

end Identity

section Composition

variable {A B A' B' A'' B'' : Type u}
variable [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [CommRing A''] [CommRing B'']
variable [Algebra A B] [Algebra A A'] [Algebra A B'] [Algebra A' B'] [Algebra B B']
variable [Algebra A' A''] [Algebra B' B''] [Algebra A' B''] [Algebra A'' B'']
variable [Algebra A A''] [Algebra A B''] [Algebra B B'']
variable [IsScalarTower A B B'] [IsScalarTower A A' B']
variable [IsScalarTower A' B' B''] [IsScalarTower A' A'' B'']
variable [IsScalarTower B B' B'']
variable [IsScalarTower A B B''] [IsScalarTower A A'' B'']

variable {M M' M'' : Type u}
variable [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
variable [AddCommGroup M'] [Module B' M'] [Module A M'] [Module A' M'] [Module B M']
variable [IsScalarTower A' B' M'] [IsScalarTower B B' M'] [IsScalarTower A A' M']
variable [AddCommGroup M''] [Module B'' M''] [Module A M''] [Module A' M''] [Module A'' M'']
variable [Module B' M''] [Module B M'']
variable [IsScalarTower B B' M'']
variable [IsScalarTower A'' B'' M''] [IsScalarTower B' B'' M''] [IsScalarTower B B'' M'']
variable [IsScalarTower A A'' M''] [IsScalarTower A' A'' M'']

/-- Principal-parts base-change maps are compatible with composition of ring squares
and module maps. -/
@[stacks 09CP]
lemma map_comp (k : ℕ) (f : M →ₗ[B] M') (g : M' →ₗ[B'] M'') :
    ((map (A := A') (B := B') (A' := A'') (B' := B'') (M := M') (M' := M'') k g :
          PrincipalParts.module A' B' M' k →ₗ[B']
            PrincipalParts.module A'' B'' M'' k).restrictScalars B) ∘ₗ
        (map (A := A) (B := B) (A' := A') (B' := B') (M := M) (M' := M') k f :
          PrincipalParts.module A B M k →ₗ[B] PrincipalParts.module A' B' M' k) =
      (map (A := A) (B := B) (A' := A'') (B' := B'') (M := M) (M' := M'') k
        (((g.restrictScalars B).comp f) : M →ₗ[B] M'') :
          PrincipalParts.module A B M k →ₗ[B] PrincipalParts.module A'' B'' M'' k) :=
  sorry

end Composition

end PrincipalParts.BaseChange

end
