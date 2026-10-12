/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.LinearAlgebra.Prod
public import stacks_project.Chap90.Definition_90_10_1_DualNumber
public import stacks_project.Chap90.Lemma_90_10_7_Pullback
public import stacks_project.Chap90.«90_17_5_3_Pullback»
public import stacks_project.Chap90.«90_17_5_3_SquareZero»

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

/-- The morphism `k[V] ⟶ k[W]` in `C_Λ` induced by a `k`-linear map `V →ₗ[k] W`. -/
def squareZeroMap {V W : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W] (f : V →ₗ[k] W) :
    squareZero Λ k V ⟶ squareZero Λ k W :=
  Hom.of ((map f).restrictScalars Λ) sorry sorry

/-- `squareZeroMap` of the identity is the identity morphism. -/
theorem squareZeroMap_id (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    squareZeroMap (LinearMap.id : V →ₗ[k] V) = 𝟙 (squareZero Λ k V) := sorry

/-- `squareZeroMap` preserves composition. -/
theorem squareZeroMap_comp {V W U : Type u}
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    [AddCommGroup U] [Module k U] [Module.Finite k U]
    (f : V →ₗ[k] W) (g : W →ₗ[k] U) :
    (squareZeroMap (g.comp f) : squareZero Λ k V ⟶ squareZero Λ k U) =
      squareZeroMap f ≫ squareZeroMap g := sorry

variable (Λ k)

/-- The functor `V ↦ k[V]` from finitely generated `k`-modules to `C_Λ`. -/
def squareZeroFunctor : FGModuleCat.{u} k ⥤ ArtinianLocalAlgCat Λ k where
  obj V := squareZero Λ k V
  map f := squareZeroMap f.hom.hom
  map_id := sorry
  map_comp := sorry

/-- `squareZeroFunctor` sends `V` to `squareZero Λ k V`. -/
theorem squareZeroFunctor_obj (V : FGModuleCat.{u} k) :
    (squareZeroFunctor Λ k).obj V = squareZero Λ k V := rfl

/-- `squareZeroFunctor` acts on morphisms by `squareZeroMap`. -/
theorem squareZeroFunctor_map {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    (squareZeroFunctor Λ k).map f = squareZeroMap f.hom.hom := rfl

/-- The identity map of carriers `k[ε] → k[k]`, as a `Λ`-algebra homomorphism. -/
def dualNumberIsoSquareZeroHom :
    (dualNumber Λ k).carrier →ₐ[Λ] (squareZero Λ k k).carrier where
  toFun := id
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- The identity map of carriers `k[k] → k[ε]`, as a `Λ`-algebra homomorphism. -/
def dualNumberIsoSquareZeroInvHom :
    (squareZero Λ k k).carrier →ₐ[Λ] (dualNumber Λ k).carrier where
  toFun := id
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- The identity-on-carriers comparison `k[ε] ≅ k[k]` in `C_Λ`. -/
def dualNumberIsoSquareZero : dualNumber Λ k ≅ squareZero Λ k k where
  hom := Hom.of (dualNumberIsoSquareZeroHom Λ k) sorry sorry
  inv := Hom.of (dualNumberIsoSquareZeroInvHom Λ k) sorry sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `dualNumberIsoSquareZero` is the identity on carriers. -/
theorem dualNumberIsoSquareZero_hom :
    (dualNumberIsoSquareZero Λ k).hom.hom = dualNumberIsoSquareZeroHom Λ k := sorry

/-- The inverse map of `dualNumberIsoSquareZero` is the identity on carriers. -/
theorem dualNumberIsoSquareZero_inv :
    (dualNumberIsoSquareZero Λ k).inv.hom = dualNumberIsoSquareZeroInvHom Λ k := sorry

variable {Λ k}

/-- The canonical inclusion `k ⟶ k[V]` in `C_Λ`. -/
def residueToSquareZero (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    residue Λ k ⟶ squareZero Λ k V :=
  Hom.of ((inlAlgHom k k V).restrictScalars Λ) sorry sorry

/-- The underlying algebra map of `residueToSquareZero` is the square-zero inclusion. -/
theorem residueToSquareZero_hom (V : Type u) [AddCommGroup V] [Module k V]
    [Module.Finite k V] :
    (residueToSquareZero V).hom = (inlAlgHom k k V).restrictScalars Λ := sorry

/-- The identification `k[0] ≅ k` in `C_Λ`, via the coefficient projection. -/
def squareZeroZeroIso : squareZero Λ k PUnit ≅ residue Λ k where
  hom := squareZeroToResidue Λ k PUnit
  inv := residueToSquareZero PUnit
  hom_inv_id := sorry
  inv_hom_id := sorry

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
      (squareZero Λ k (V × W)).carrier where
  toFun := squareZeroBinaryIsoInvFun V W
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- The identification `k[V × W] ≅ k[V] ×_k k[W]` in `C_Λ`. -/
def squareZeroBinaryIso (V W : Type u)
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W] :
    squareZero Λ k (V × W) ≅ squareZeroPullback (squareZero Λ k V) W where
  hom := Hom.of (squareZeroBinaryIsoHom V W) sorry sorry
  inv := Hom.of (squareZeroBinaryIsoInvHom V W) sorry sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

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

/-- Scaling of dual numbers in the `ε`-direction by `r : k`. -/
def dualNumberSMul (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k]
    [Algebra Λ k] [Module.Finite Λ k] (r : k) :
    dualNumber Λ k ⟶ dualNumber Λ k :=
  Hom.of ((map (LinearMap.lsmul k k r)).restrictScalars Λ) sorry sorry

/-- The underlying algebra map of `dualNumberSMul r` is `TrivSqZeroExt.map` of scaling. -/
theorem dualNumberSMul_hom (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k]
    [Algebra Λ k] [Module.Finite Λ k] (r : k) :
    (dualNumberSMul Λ k r).hom = (map (LinearMap.lsmul k k r)).restrictScalars Λ := sorry

/-- The algebra map adding the two `ε`-coefficients of a pair in `k[ε] ×_k k[ε]`. -/
def dualNumberSumHom :
    (dualNumberPullback (dualNumber Λ k)).carrier →ₐ[Λ] (dualNumber Λ k).carrier where
  toFun p :=
    let fstP :=
      AlgHom.pullbackFst (toResidue (dualNumber Λ k)).hom (dualNumberToResidue Λ k).hom p
    let sndP :=
      AlgHom.pullbackSnd (toResidue (dualNumber Λ k)).hom (dualNumberToResidue Λ k).hom p
    ⟨fstP.fst, fstP.snd + sndP.snd⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- The sum map `k[ε] ×_k k[ε] ⟶ k[ε]` in `C_Λ`. -/
def dualNumberSum : dualNumberPullback (dualNumber Λ k) ⟶ dualNumber Λ k :=
  Hom.of dualNumberSumHom sorry sorry

/-- The underlying algebra map of `dualNumberSum` is `dualNumberSumHom`. -/
theorem dualNumberSum_hom (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k]
    [Algebra Λ k] [Module.Finite Λ k] :
    (dualNumberSum : dualNumberPullback (dualNumber Λ k) ⟶ dualNumber Λ k).hom =
      dualNumberSumHom := sorry

end ArtinianLocalAlgCat
