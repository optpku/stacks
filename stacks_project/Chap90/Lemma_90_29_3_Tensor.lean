module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import stacks_project.Chap90.Lemma_90_12_2_SquareZero
public import stacks_project.Chap90.Lemma_90_12_2_Tensor
public import stacks_project.Chap90.Lemma_90_29_2_Instances
public import stacks_project.Chap90.Lemma_90_29_2_IsoClass
public import stacks_project.Chap90.Situation_90_29_1_Pullback

/-!
# Residue-change comparison of tangent spaces

A finite residue-field extension `k → l` identifies `k[lε]` with the square-zero
extension `k[l]`, and therefore supplies a canonical `l`-linear map
`T p ⊗[k] l ⟶ T(p_{l/k})` on dual-number fibres of isomorphism-class functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory hiding Linear
open CategoryTheory.Functor
open ArtinianLocalAlgCat
open TrivSqZeroExt
open scoped TensorProduct

universe u v w

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]

namespace ArtinianLocalAlgCat

/-- The underlying algebra map of `residueChangeDualNumberIso`, sending a matching
pair `(d, x)` in `l[ε] ×_l k` to the square-zero element `⟨x, d.snd⟩` in `k[l]`. -/
def residueChangeDualNumberIsoHom :
    (residueChange k (dualNumber Λ l)).carrier →ₐ[Λ] (squareZero Λ k l).carrier where
  toFun z :=
    let d :=
      AlgHom.pullbackFst (toResidue (dualNumber Λ l)).hom (IsScalarTower.toAlgHom Λ k l) z
    let x :=
      AlgHom.pullbackSnd (toResidue (dualNumber Λ l)).hom (IsScalarTower.toAlgHom Λ k l) z
    ⟨x, d.snd⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- The inverse algebra map of `residueChangeDualNumberIso`, sending `⟨a, b⟩` in `k[l]`
to the matching pair `(⟨algebraMap k l a, b⟩, a)` in `l[ε] ×_l k`. -/
def residueChangeDualNumberIsoInvHom :
    (squareZero Λ k l).carrier →ₐ[Λ] (residueChange k (dualNumber Λ l)).carrier where
  toFun z :=
    ⟨(⟨algebraMap k l z.fst, z.snd⟩, z.fst), sorry⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- The identification `k[lε] ≅ k[l]` in `C_{Λ, k}`, comparing residue change of
`l[ε]` with the trivial square-zero extension on `l`. -/
def residueChangeDualNumberIso :
    residueChange k (dualNumber Λ l) ≅ squareZero Λ k l where
  hom :=
    { hom := residueChangeDualNumberIsoHom Λ k l
      isLocalHom := sorry
      residue_compat := sorry }
  inv :=
    { hom := residueChangeDualNumberIsoInvHom Λ k l
      isLocalHom := sorry
      residue_compat := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward morphism of `residueChangeDualNumberIso` is
`residueChangeDualNumberIsoHom`. -/
theorem residueChangeDualNumberIso_hom :
    (residueChangeDualNumberIso Λ k l).hom.hom = residueChangeDualNumberIsoHom Λ k l :=
  sorry

/-- The inverse morphism of `residueChangeDualNumberIso` is
`residueChangeDualNumberIsoInvHom`. -/
theorem residueChangeDualNumberIso_inv :
    (residueChangeDualNumberIso Λ k l).inv.hom = residueChangeDualNumberIsoInvHom Λ k l :=
  sorry

/-- `residueChangeDualNumberIsoHom` sends a matching pair to the corresponding
square-zero element of `k[l]`. -/
theorem residueChangeDualNumberIsoHom_apply
    (z : (residueChange k (dualNumber Λ l)).carrier) :
    residueChangeDualNumberIsoHom Λ k l z =
      ⟨AlgHom.pullbackSnd (toResidue (dualNumber Λ l)).hom (IsScalarTower.toAlgHom Λ k l) z,
        (AlgHom.pullbackFst (toResidue (dualNumber Λ l)).hom
          (IsScalarTower.toAlgHom Λ k l) z).snd⟩ :=
  sorry

namespace residueChangeOver

variable {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)
variable [IsPredeformationCategory p] [HasSchlessingerH2 (fiberIsoClassFunctor p)]

/-- If `fiberIsoClassFunctor p` satisfies Schlessinger's (H2), then so does the
isomorphism-class functor of the residue-change reindexing `p_{l/k}`. -/
instance instHasSchlessingerH2_fiberIsoClass :
    HasSchlessingerH2 (fiberIsoClassFunctor (residueChangeOver Λ k l p)) :=
  sorry

/-- Right `l`-module structure on `T p ⊗[k] l`, acting on the second factor. -/
instance instModule_tangentSpaceTensor :
    Module l ((fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] l) where
  smul a x := TensorProduct.map LinearMap.id (LinearMap.mulLeft k a) x
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The canonical `l`-linear comparison `T p ⊗[k] l ⟶ T(p_{l/k})`, obtained by
identifying `F_{l/k}(l[ε])` with `F(k[lε])` and `k[lε]` with `k[l]`. -/
def tangentSpaceTensor :
    (fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] l →ₗ[l]
      (fiberIsoClassFunctor (residueChangeOver Λ k l p)).obj (dualNumber Λ l) where
  toFun x :=
    (isoClassEquiv Λ k l p (dualNumber Λ l)).symm
      ((fiberIsoClassFunctor p).map (residueChangeDualNumberIso Λ k l).inv
        (fiberDualTangentTensor_of p l x))
  map_add' := sorry
  map_smul' := sorry

/-- `tangentSpaceTensor` is the composite of `fiberDualTangentTensor_of`, the
square-zero identification of `k[lε]`, and `isoClassEquiv.symm`. -/
theorem tangentSpaceTensor_spec
    (x : (fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] l) :
    tangentSpaceTensor Λ k l p x =
      (isoClassEquiv Λ k l p (dualNumber Λ l)).symm
        ((fiberIsoClassFunctor p).map (residueChangeDualNumberIso Λ k l).inv
          (fiberDualTangentTensor_of p l x)) :=
  sorry

/-- On pure tensors, `tangentSpaceTensor` applies the dual-number/square-zero
comparison to `fiberDualTangentTensor_of` and transports along `isoClassEquiv`. -/
theorem tangentSpaceTensor_tmul
    (x : (fiberIsoClassFunctor p).obj (dualNumber Λ k)) (a : l) :
    tangentSpaceTensor Λ k l p (x ⊗ₜ a) =
      (isoClassEquiv Λ k l p (dualNumber Λ l)).symm
        ((fiberIsoClassFunctor p).map (residueChangeDualNumberIso Λ k l).inv
          (fiberDualTangentTensor_of p l (x ⊗ₜ a))) :=
  sorry

end residueChangeOver

end ArtinianLocalAlgCat
