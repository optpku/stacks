module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SquareZeroFunctor
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange.Properties
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange.IsoClass

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
    (residueChange k (dualNumber Λ l)).carrier →ₐ[Λ] (squareZero Λ k l).carrier := by
  let f : (residueChange k (dualNumber Λ l)).carrier → (squareZero Λ k l).carrier := fun z =>
    let d :=
      AlgHom.pullbackFst (toResidue (dualNumber Λ l)).hom (IsScalarTower.toAlgHom Λ k l) z
    let x :=
      AlgHom.pullbackSnd (toResidue (dualNumber Λ l)).hom (IsScalarTower.toAlgHom Λ k l) z
    ⟨x, d.snd⟩
  have laws : f 1 = 1 ∧ (∀ x y, f (x * y) = f x * f y) ∧ f 0 = 0 ∧
      (∀ x y, f (x + y) = f x + f y) ∧
      (∀ a : Λ, f (algebraMap Λ _ a) = algebraMap Λ _ a) := by
    sorry
  exact
    { toFun := f
      map_one' := laws.1
      map_mul' := laws.2.1
      map_zero' := laws.2.2.1
      map_add' := laws.2.2.2.1
      commutes' := laws.2.2.2.2 }

/-- The inverse algebra map sends `⟨a, b⟩` in `k[l]` to the matching pair
`(⟨algebraMap k l a, b⟩, a)` in `l[ε] ×_l k`. -/
def residueChangeDualNumberIsoInvHom :
    (squareZero Λ k l).carrier →ₐ[Λ] (residueChange k (dualNumber Λ l)).carrier := by
  let pair : (squareZero Λ k l).carrier → (dualNumber Λ l).carrier × k :=
    fun z => (⟨algebraMap k l z.fst, z.snd⟩, z.fst)
  let matching := ∀ z, pair z ∈
    AlgHom.pullback (toResidue (dualNumber Λ l)).hom (IsScalarTower.toAlgHom Λ k l)
  let f (h : matching) : (squareZero Λ k l).carrier →
      (residueChange k (dualNumber Λ l)).carrier := fun z => ⟨pair z, h z⟩
  have laws : matching ∧ ∀ h : matching,
      f h 1 = 1 ∧ (∀ x y, f h (x * y) = f h x * f h y) ∧ f h 0 = 0 ∧
      (∀ x y, f h (x + y) = f h x + f h y) ∧
      (∀ a : Λ, f h (algebraMap Λ _ a) = algebraMap Λ _ a) := by
    sorry
  exact
    { toFun := f laws.1
      map_one' := (laws.2 laws.1).1
      map_mul' := (laws.2 laws.1).2.1
      map_zero' := (laws.2 laws.1).2.2.1
      map_add' := (laws.2 laws.1).2.2.2.1
      commutes' := (laws.2 laws.1).2.2.2.2 }

/-- The residue change of `l[ε]` is canonically isomorphic to the trivial
square-zero extension `k[l]` in the category of Artinian local algebras. -/
def residueChangeDualNumberIso :
    residueChange k (dualNumber Λ l) ≅ squareZero Λ k l := by
  let f := residueChangeDualNumberIsoHom Λ k l
  let g := residueChangeDualNumberIsoInvHom Λ k l
  have laws :
      (IsLocalHom f ∧ ∀ hf : IsLocalHom f,
        residueCompat f hf = residueIsoHom (residueChange k (dualNumber Λ l))) ∧
      (IsLocalHom g ∧ ∀ hg : IsLocalHom g,
        residueCompat g hg = residueIsoHom (squareZero Λ k l)) ∧
      (∀ (hf : IsLocalHom f) (hr : residueCompat f hf =
          residueIsoHom (residueChange k (dualNumber Λ l)))
        (hg : IsLocalHom g) (hs : residueCompat g hg = residueIsoHom (squareZero Λ k l)),
        ((Hom.of f hf hr : residueChange k (dualNumber Λ l) ⟶ squareZero Λ k l) ≫
          (Hom.of g hg hs : squareZero Λ k l ⟶ residueChange k (dualNumber Λ l)) =
            𝟙 (residueChange k (dualNumber Λ l))) ∧
        ((Hom.of g hg hs : squareZero Λ k l ⟶ residueChange k (dualNumber Λ l)) ≫
          (Hom.of f hf hr : residueChange k (dualNumber Λ l) ⟶ squareZero Λ k l) =
            𝟙 (squareZero Λ k l))) := by
    sorry
  exact
    { hom := Hom.of f laws.1.1 (laws.1.2 laws.1.1)
      inv := Hom.of g laws.2.1.1 (laws.2.1.2 laws.2.1.1)
      hom_inv_id := (laws.2.2 _ _ _ _).1
      inv_hom_id := (laws.2.2 _ _ _ _).2 }

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
    Module l ((fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] l) := by
  let smul : l → (fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] l →
      (fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] l :=
    fun a x => TensorProduct.map LinearMap.id (LinearMap.mulLeft k a) x
  have laws : (∀ x, smul 1 x = x) ∧
      (∀ a b x, smul (a * b) x = smul a (smul b x)) ∧
      (∀ a, smul a 0 = 0) ∧ (∀ a x y, smul a (x + y) = smul a x + smul a y) ∧
      (∀ a b x, smul (a + b) x = smul a x + smul b x) ∧ (∀ x, smul 0 x = 0) := by
    sorry
  exact
    { smul := smul
      one_smul := laws.1
      mul_smul := laws.2.1
      smul_zero := laws.2.2.1
      smul_add := laws.2.2.2.1
      add_smul := laws.2.2.2.2.1
      zero_smul := laws.2.2.2.2.2 }

/-- The canonical `l`-linear comparison `T p ⊗[k] l ⟶ T(p_{l/k})` identifies
`F_{l/k}(l[ε])` with `F(k[lε])` and `k[lε]` with `k[l]`. -/
def tangentSpaceTensor :
    (fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] l →ₗ[l]
      (fiberIsoClassFunctor (residueChangeOver Λ k l p)).obj (dualNumber Λ l) := by
  let f : (fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] l →
      (fiberIsoClassFunctor (residueChangeOver Λ k l p)).obj (dualNumber Λ l) := fun x =>
    (isoClassEquiv Λ k l p (dualNumber Λ l)).symm
      ((fiberIsoClassFunctor p).map (residueChangeDualNumberIso Λ k l).inv
        (fiberDualTangentTensor_of p l x))
  have laws : (∀ x y, f (x + y) = f x + f y) ∧
      (∀ a : l, ∀ x, f (a • x) = a • f x) := by
    sorry
  exact { toFun := f, map_add' := laws.1, map_smul' := laws.2 }

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

/-- The canonical linear comparison from the scalar extension of a tangent space
to the tangent space after finite residue-field change is bijective. -/
theorem bijective_tangentSpaceTensor :
    Function.Bijective (tangentSpaceTensor Λ k l p) :=
  sorry

end residueChangeOver

end ArtinianLocalAlgCat
