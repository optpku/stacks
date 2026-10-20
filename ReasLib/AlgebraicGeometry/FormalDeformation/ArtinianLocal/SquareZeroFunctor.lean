/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.LinearAlgebra.Prod
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.DualNumberPullback
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SquareZeroMap
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SquareZeroPullback
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.Operations

/-!
# Square-zero extensions as a functor of finite `k`-modules

The assignment `V ↦ k[V]` is the functor `FGModuleCat k ⥤ ArtinianLocalAlgCat Λ k`
sending a finite-dimensional `k`-vector space to the trivial square-zero extension
`TrivSqZeroExt k V` in `C_Λ`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open TrivSqZeroExt

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

variable (Λ k)

/-- The functor `V ↦ k[V]` from finitely generated `k`-modules to `C_Λ`. -/
def squareZeroFunctor : FGModuleCat.{u} k ⥤ ArtinianLocalAlgCat Λ k where
  obj V := squareZero Λ k V
  map f := squareZeroMap f.hom.hom
  map_id V := squareZeroMap_id V
  map_comp f g := squareZeroMap_comp f.hom.hom g.hom.hom

/-- `squareZeroFunctor` sends `V` to `squareZero Λ k V`. -/
theorem squareZeroFunctor_obj (V : FGModuleCat.{u} k) :
    (squareZeroFunctor Λ k).obj V = squareZero Λ k V := rfl

/-- `squareZeroFunctor` acts on morphisms by `squareZeroMap`. -/
theorem squareZeroFunctor_map {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    (squareZeroFunctor Λ k).map f = squareZeroMap f.hom.hom := rfl

/-- The identity map of carriers `k[ε] → k[k]`, as a `Λ`-algebra homomorphism. -/
def dualNumberIsoSquareZeroHom :
    (dualNumber Λ k).carrier →ₐ[Λ] (squareZero Λ k k).carrier := by
  let identity : (dualNumber Λ k).carrier → (squareZero Λ k k).carrier := id
  have laws : identity 1 = 1 ∧
      (∀ left right, identity (left * right) = identity left * identity right) ∧
      identity 0 = 0 ∧
      (∀ left right, identity (left + right) = identity left + identity right) ∧
      (∀ scalar : Λ, identity (algebraMap Λ _ scalar) = algebraMap Λ _ scalar) := sorry
  exact { toFun := identity
          map_one' := laws.1
          map_mul' := laws.2.1
          map_zero' := laws.2.2.1
          map_add' := laws.2.2.2.1
          commutes' := laws.2.2.2.2 }

/-- The identity map of carriers `k[k] → k[ε]`, as a `Λ`-algebra homomorphism. -/
def dualNumberIsoSquareZeroInvHom :
    (squareZero Λ k k).carrier →ₐ[Λ] (dualNumber Λ k).carrier := by
  let identity : (squareZero Λ k k).carrier → (dualNumber Λ k).carrier := id
  have laws : identity 1 = 1 ∧
      (∀ left right, identity (left * right) = identity left * identity right) ∧
      identity 0 = 0 ∧
      (∀ left right, identity (left + right) = identity left + identity right) ∧
      (∀ scalar : Λ, identity (algebraMap Λ _ scalar) = algebraMap Λ _ scalar) := sorry
  exact { toFun := identity
          map_one' := laws.1
          map_mul' := laws.2.1
          map_zero' := laws.2.2.1
          map_add' := laws.2.2.2.1
          commutes' := laws.2.2.2.2 }

/-- The identity-on-carriers comparison `k[ε] ≅ k[k]` in `C_Λ`. -/
def dualNumberIsoSquareZero : dualNumber Λ k ≅ squareZero Λ k k := by
  let forward := dualNumberIsoSquareZeroHom Λ k
  let backward := dualNumberIsoSquareZeroInvHom Λ k
  have laws :
      (IsLocalHom forward ∧ ∀ localness : IsLocalHom forward,
        residueCompat forward localness = residueIsoHom (dualNumber Λ k)) ∧
      (IsLocalHom backward ∧ ∀ localness : IsLocalHom backward,
        residueCompat backward localness = residueIsoHom (squareZero Λ k k)) ∧
      (∀ (hom : dualNumber Λ k ⟶ squareZero Λ k k)
          (inv : squareZero Λ k k ⟶ dualNumber Λ k),
        hom.hom = forward → inv.hom = backward →
          hom ≫ inv = 𝟙 (dualNumber Λ k) ∧ inv ≫ hom = 𝟙 (squareZero Λ k k)) := sorry
  let hom := Hom.of forward laws.1.1 (laws.1.2 laws.1.1)
  let inv := Hom.of backward laws.2.1.1 (laws.2.1.2 laws.2.1.1)
  exact { hom := hom, inv := inv
          hom_inv_id := (laws.2.2 hom inv rfl rfl).1
          inv_hom_id := (laws.2.2 hom inv rfl rfl).2 }

/-- The forward map of `dualNumberIsoSquareZero` is the identity on carriers. -/
theorem dualNumberIsoSquareZero_hom :
    (dualNumberIsoSquareZero Λ k).hom.hom = dualNumberIsoSquareZeroHom Λ k := sorry

/-- The inverse map of `dualNumberIsoSquareZero` is the identity on carriers. -/
theorem dualNumberIsoSquareZero_inv :
    (dualNumberIsoSquareZero Λ k).inv.hom = dualNumberIsoSquareZeroInvHom Λ k := sorry

variable {Λ k}

/-- The canonical inclusion `k ⟶ k[V]` in `C_Λ`. -/
def residueToSquareZero (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    residue Λ k ⟶ squareZero Λ k V := by
  let hom : (residue Λ k).carrier →ₐ[Λ] (squareZero Λ k V).carrier :=
    (inlAlgHom k k V).restrictScalars Λ
  have laws : IsLocalHom hom ∧ ∀ localness : IsLocalHom hom,
      residueCompat hom localness = residueIsoHom (residue Λ k) := sorry
  exact Hom.of hom laws.1 (laws.2 laws.1)

/-- The underlying algebra map of `residueToSquareZero` is the square-zero inclusion. -/
theorem residueToSquareZero_hom (V : Type u) [AddCommGroup V] [Module k V]
    [Module.Finite k V] :
    (residueToSquareZero V).hom = (inlAlgHom k k V).restrictScalars Λ := sorry

/-- The identification `k[0] ≅ k` in `C_Λ`, via the coefficient projection. -/
def squareZeroZeroIso : squareZero Λ k PUnit ≅ residue Λ k := by
  let hom := squareZeroToResidue Λ k PUnit
  let inv := residueToSquareZero (Λ := Λ) (k := k) PUnit
  have laws : hom ≫ inv = 𝟙 (squareZero Λ k PUnit) ∧
      inv ≫ hom = 𝟙 (residue Λ k) := sorry
  exact { hom := hom, inv := inv, hom_inv_id := laws.1, inv_hom_id := laws.2 }

/-- The forward map of `squareZeroZeroIso` is the coefficient projection. -/
theorem squareZeroZeroIso_hom (Λ k : Type u)
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k] :
    (squareZeroZeroIso : squareZero Λ k PUnit ≅ residue Λ k).hom =
      squareZeroToResidue Λ k PUnit :=
  rfl

/-- The algebra map `k[V × W] → k[V] × k[W]` used to build `squareZeroBinaryIso`. -/
def squareZeroBinaryIsoHom (V W : Type u)
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W] :
    (squareZero Λ k (V × W)).carrier →ₐ[Λ]
      (squareZeroPullback (squareZero Λ k V) W).carrier :=
  AlgHom.codRestrict
    (AlgHom.prod ((map (LinearMap.fst k V W)).restrictScalars Λ)
      ((map (LinearMap.snd k V W)).restrictScalars Λ))
    (AlgHom.pullback (toResidue (squareZero Λ k V)).hom (squareZeroToResidue Λ k W).hom)
    sorry

/-- The inverse algebra map of `squareZeroBinaryIso`, reconstructing `k[V × W]`
from a matching pair in `k[V] ×_k k[W]`. -/
def squareZeroBinaryIsoInvFun (V W : Type u)
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (p : (squareZeroPullback (squareZero Λ k V) W).carrier) :
    (squareZero Λ k (V × W)).carrier :=
  let fstP :=
    AlgHom.pullbackFst (toResidue (squareZero Λ k V)).hom (squareZeroToResidue Λ k W).hom p
  let sndP :=
    AlgHom.pullbackSnd (toResidue (squareZero Λ k V)).hom (squareZeroToResidue Λ k W).hom p
  ⟨fstP.fst, (fstP.snd, sndP.snd)⟩

/-- The inverse algebra map of `squareZeroBinaryIso`. -/
def squareZeroBinaryIsoInvHom (V W : Type u)
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W] :
    (squareZeroPullback (squareZero Λ k V) W).carrier →ₐ[Λ]
      (squareZero Λ k (V × W)).carrier := by
  let reconstruction := squareZeroBinaryIsoInvFun (Λ := Λ) (k := k) V W
  have laws : reconstruction 1 = 1 ∧
      (∀ left right, reconstruction (left * right) = reconstruction left * reconstruction right) ∧
      reconstruction 0 = 0 ∧
      (∀ left right, reconstruction (left + right) = reconstruction left + reconstruction right) ∧
      (∀ scalar : Λ, reconstruction (algebraMap Λ _ scalar) = algebraMap Λ _ scalar) := sorry
  exact { toFun := reconstruction
          map_one' := laws.1
          map_mul' := laws.2.1
          map_zero' := laws.2.2.1
          map_add' := laws.2.2.2.1
          commutes' := laws.2.2.2.2 }

/-- The identification `k[V × W] ≅ k[V] ×_k k[W]` in `C_Λ`. -/
def squareZeroBinaryIso (V W : Type u)
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W] :
    squareZero Λ k (V × W) ≅ squareZeroPullback (squareZero Λ k V) W := by
  let forward := squareZeroBinaryIsoHom (Λ := Λ) (k := k) V W
  let backward := squareZeroBinaryIsoInvHom (Λ := Λ) (k := k) V W
  have laws :
      (IsLocalHom forward ∧ ∀ localness : IsLocalHom forward,
        residueCompat forward localness = residueIsoHom (squareZero Λ k (V × W))) ∧
      (IsLocalHom backward ∧ ∀ localness : IsLocalHom backward,
        residueCompat backward localness = residueIsoHom (squareZeroPullback (squareZero Λ k V) W)) ∧
      (∀ (hom : squareZero Λ k (V × W) ⟶ squareZeroPullback (squareZero Λ k V) W)
          (inv : squareZeroPullback (squareZero Λ k V) W ⟶ squareZero Λ k (V × W)),
        hom.hom = forward → inv.hom = backward →
          hom ≫ inv = 𝟙 (squareZero Λ k (V × W)) ∧
            inv ≫ hom = 𝟙 (squareZeroPullback (squareZero Λ k V) W)) := sorry
  let hom := Hom.of forward laws.1.1 (laws.1.2 laws.1.1)
  let inv := Hom.of backward laws.2.1.1 (laws.2.1.2 laws.2.1.1)
  exact { hom := hom, inv := inv
          hom_inv_id := (laws.2.2 hom inv rfl rfl).1
          inv_hom_id := (laws.2.2 hom inv rfl rfl).2 }

/-- The first projection of `squareZeroBinaryIso` recovers `squareZeroMap` of `LinearMap.fst`. -/
theorem squareZeroBinaryIso_comp_fst (V W : Type u)
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W] :
    (squareZeroBinaryIso V W).hom ≫ squareZeroPullbackFst (squareZero Λ k V) W =
      squareZeroMap (LinearMap.fst k V W) := sorry

/-- The second projection of `squareZeroBinaryIso` recovers `squareZeroMap` of `LinearMap.snd`. -/
theorem squareZeroBinaryIso_comp_snd (V W : Type u)
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W] :
    (squareZeroBinaryIso V W).hom ≫ squareZeroPullbackSnd (squareZero Λ k V) W =
      squareZeroMap (LinearMap.snd k V W) := sorry

/-- Addition `V × V →ₗ[k] V` as a linear map. -/
def squareZeroAddMap (V : Type u) [AddCommGroup V] [Module k V] : V × V →ₗ[k] V :=
  LinearMap.fst k V V + LinearMap.snd k V V

/-- The sum map `k[V] ×_k k[V] ⟶ k[V]` induced by addition on `V`. -/
def squareZeroSum (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    squareZeroPullback (squareZero Λ k V) V ⟶ squareZero Λ k V :=
  (squareZeroBinaryIso V V).inv ≫ squareZeroMap (squareZeroAddMap V)

/-- `squareZeroAddMap` sends a pair to the sum of its components. -/
theorem squareZeroAddMap_apply (V : Type u) [AddCommGroup V] [Module k V] (x y : V) :
    (squareZeroAddMap V : V × V →ₗ[k] V) (x, y) = x + y := sorry

/-- Composing the binary iso with `squareZeroSum` recovers addition on `V`. -/
theorem squareZeroSum_comp_binaryIso (V : Type u)
    [AddCommGroup V] [Module k V] [Module.Finite k V] :
    (squareZeroBinaryIso V V).hom ≫ squareZeroSum V =
      (squareZeroMap (squareZeroAddMap V) :
        squareZero Λ k (V × V) ⟶ squareZero Λ k V) := sorry

/-- The underlying algebra map of `dualNumberScaleHom r` is `TrivSqZeroExt.map` of scaling. -/
theorem dualNumberScaleHom_hom (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k]
    [Algebra Λ k] [Module.Finite Λ k] (r : k) :
    (dualNumberScaleHom Λ r).hom = (map (LinearMap.lsmul k k r)).restrictScalars Λ := sorry

/-- The algebra map adding the two `ε`-coefficients of a pair in `k[ε] ×_k k[ε]`. -/
def dualNumberSumHom :
    (dualNumberPullback (dualNumber Λ k)).carrier →ₐ[Λ] (dualNumber Λ k).carrier := by
  let addition : (dualNumberPullback (dualNumber Λ k)).carrier →
      (dualNumber Λ k).carrier := fun p ↦
    let fstP :=
      AlgHom.pullbackFst (toResidue (dualNumber Λ k)).hom (dualNumberToResidue Λ k).hom p
    let sndP :=
      AlgHom.pullbackSnd (toResidue (dualNumber Λ k)).hom (dualNumberToResidue Λ k).hom p
    ⟨fstP.fst, fstP.snd + sndP.snd⟩
  have laws : addition 1 = 1 ∧
      (∀ left right, addition (left * right) = addition left * addition right) ∧
      addition 0 = 0 ∧
      (∀ left right, addition (left + right) = addition left + addition right) ∧
      (∀ scalar : Λ, addition (algebraMap Λ _ scalar) = algebraMap Λ _ scalar) := sorry
  exact { toFun := addition
          map_one' := laws.1
          map_mul' := laws.2.1
          map_zero' := laws.2.2.1
          map_add' := laws.2.2.2.1
          commutes' := laws.2.2.2.2 }

/-- The sum map `k[ε] ×_k k[ε] ⟶ k[ε]` in `C_Λ`. -/
def dualNumberSum : dualNumberPullback (dualNumber Λ k) ⟶ dualNumber Λ k := by
  let hom := dualNumberSumHom (Λ := Λ) (k := k)
  have laws : IsLocalHom hom ∧ ∀ localness : IsLocalHom hom,
      residueCompat hom localness = residueIsoHom (dualNumberPullback (dualNumber Λ k)) := sorry
  exact Hom.of hom laws.1 (laws.2 laws.1)

/-- The underlying algebra map of `dualNumberSum` is `dualNumberSumHom`. -/
theorem dualNumberSum_hom (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k]
    [Algebra Λ k] [Module.Finite Λ k] :
    (dualNumberSum : dualNumberPullback (dualNumber Λ k) ⟶ dualNumber Λ k).hom =
      dualNumberSumHom := sorry

end ArtinianLocalAlgCat
