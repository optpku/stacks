/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Lemma_90_12_2_SquareZero
public import stacks_project.Chap90.Lemma_90_19_9_Module
public import stacks_project.Chap90.Lemma_90_29_3_Tensor
public import stacks_project.Chap90.Remark_90_19_4_InfinitesimalAut

/-!
# Residue-change comparison of infinitesimal automorphisms

A finite residue-field extension `k → l` identifies `k[lε]` with the square-zero
extension `k[l]`, and therefore supplies a canonical `l`-linear map
`Inf(p) ⊗[k] l ⟶ Inf(p_{l/k})` on dual-number infinitesimal automorphism spaces.
-/

@[expose] public section

noncomputable section

open CategoryTheory hiding Linear
open CategoryTheory.Functor
open CategoryTheory.Functor.Chosen
open CategoryTheory.Functor.Fiber
open ArtinianLocalAlgCat
open scoped TensorProduct

universe u v w

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]

namespace ArtinianLocalAlgCat

/-- The inverse algebra map of `residueChangeResidueIso`, sending `x : k` to the matching
pair `(algebraMap k l x, x)` in `l ×_l k`. -/
def residueChangeResidueIsoInvHom :
    (residue Λ k).carrier →ₐ[Λ] (residueChange k (residue Λ l)).carrier where
  toFun x := ⟨(algebraMap k l x, x), sorry⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- The identification `l ×_l k ≅ k` in `C_{Λ, k}`, comparing residue change of the residue
object `l` with the residue object `k`. -/
def residueChangeResidueIso :
    residueChange k (residue Λ l) ≅ residue Λ k where
  hom := residueChangeSnd k (residue Λ l)
  inv :=
    { hom := residueChangeResidueIsoInvHom Λ k l
      isLocalHom := sorry
      residue_compat := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The inverse morphism of `residueChangeResidueIso` is `residueChangeResidueIsoInvHom`. -/
theorem residueChangeResidueIso_inv :
    (residueChangeResidueIso Λ k l).inv.hom = residueChangeResidueIsoInvHom Λ k l :=
  sorry

namespace residueChangeOver

variable {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)
variable [IsDeformationCategory p]

/-- A deformation category satisfies the Rim-Schlessinger condition (RS). -/
instance instHasRimSchlessinger_ofIsDeformationCategory :
    HasRimSchlessinger p :=
  IsDeformationCategory.hasRimSchlessinger

/-- The object `k → k[ε]` of `Under (residue Λ k)`. -/
def infAutDualNumberUnder : Under (residue Λ k) :=
  Under.mk (residueToDualNumber Λ k)

/-- The object `k → k[l]` of `Under (residue Λ k)`, after the dual-number/square-zero
identification and scalar extension `Algebra.linearMap k l`. -/
def infAutSquareZeroUnder : Under (residue Λ k) :=
  Under.mk
    (residueToDualNumber Λ k ≫ (dualNumberIsoSquareZero Λ k).hom ≫
      squareZeroMap (Algebra.linearMap k l))

/-- The object `k → k[lε]` of `Under (residue Λ k)`, after identifying `k[l]` with
residue change of `l[ε]`. -/
def infAutResidueChangeDualNumberUnder : Under (residue Λ k) :=
  Under.mk
    (residueToDualNumber Λ k ≫ (dualNumberIsoSquareZero Λ k).hom ≫
      squareZeroMap (Algebra.linearMap k l) ≫
        (residueChangeDualNumberIso Λ k l).inv)

/-- The Under-morphism `(k → k[ε]) ⟶ (k → k[l])` induced by
`dualNumberIsoSquareZero.hom ≫ squareZeroMap (Algebra.linearMap k l)`. -/
def infAutSquareZeroHom : infAutDualNumberUnder Λ k ⟶ infAutSquareZeroUnder Λ k l :=
  Under.homMk
    ((dualNumberIsoSquareZero Λ k).hom ≫ squareZeroMap (Algebra.linearMap k l)) sorry

/-- The Under-morphism `(k → k[l]) ⟶ (k → k[lε])` induced by
`residueChangeDualNumberIso.inv`. -/
def infAutResidueChangeDualNumberHom :
    infAutSquareZeroUnder Λ k l ⟶ infAutResidueChangeDualNumberUnder Λ k l :=
  Under.homMk (residueChangeDualNumberIso Λ k l).inv sorry

/-- The Under-morphism `(k → l ×_l k) ⟶ (k → k[lε])` induced by residue change of
`residueToDualNumber`. -/
def infAutCorrespondingHom :
    Under.mk (residueChangeResidueIso Λ k l).inv ⟶ infAutResidueChangeDualNumberUnder Λ k l :=
  Under.homMk ((residueChangeFunctor Λ k l).map (residueToDualNumber Λ l)) sorry

/-- The object of `F(l ×_l k)` corresponding to the chosen residue-fibre object of `p`. -/
def correspondingResidueObj :
    p.Fiber ((residueChangeFunctor Λ k l).obj (residue Λ l)) :=
  pushforwardObj p (residueChangeResidueIso Λ k l).inv (chosenResidueFiberObj p)

/-- The object of `F(k[lε])` obtained by pushing the chosen residue-fibre object of `p`
along the dual-number/square-zero/residue-change composite. -/
def correspondingDualNumberObj :
    p.Fiber ((residueChangeFunctor Λ k l).obj (dualNumber Λ l)) :=
  pushforwardObj p (infAutResidueChangeDualNumberUnder Λ k l).hom (chosenResidueFiberObj p)

/-- The object of `F_{l/k}` over `l` corresponding to the chosen residue-fibre object of `p`. -/
def correspondingResidueFiber :
    (residueChangeOver Λ k l p).Fiber (residue Λ l) :=
  (fiberMk Λ k l p (residue Λ l)).obj (correspondingResidueObj Λ k l p)

/-- The object of `F_{l/k}` over `l[ε]` obtained by `fiberMk` of
`correspondingDualNumberObj`. -/
def correspondingDualNumberFiber :
    (residueChangeOver Λ k l p).Fiber (dualNumber Λ l) :=
  (fiberMk Λ k l p (dualNumber Λ l)).obj (correspondingDualNumberObj Λ k l p)

/-- The dual-number pushforward of `correspondingResidueFiber` in `F_{l/k}`, as the
pullback morphism with first component `residueToDualNumber` and second component
the selected comparison of the two pushforwards of the chosen residue object. -/
def infAutFiberMkPushforwardHom :
    fiberInclusion.obj (correspondingResidueFiber Λ k l p) ⟶
      fiberInclusion.obj (correspondingDualNumberFiber Λ k l p) where
  fst := residueToDualNumber Λ l
  snd := pushforwardComparison p (infAutCorrespondingHom Λ k l) (chosenResidueFiberObj p)
  w := sorry

/-- `infAutFiberMkPushforwardHom` lies over `residueToDualNumber`. -/
instance instIsHomLift_infAutFiberMkPushforwardHom :
    (residueChangeOver Λ k l p).IsHomLift (residueToDualNumber Λ l)
      (infAutFiberMkPushforwardHom Λ k l p) :=
  sorry

/-- `infAutFiberMkPushforwardHom` is strongly cocartesian over `residueToDualNumber`. -/
instance instIsStronglyCocartesian_infAutFiberMkPushforwardHom :
    (residueChangeOver Λ k l p).IsStronglyCocartesian (residueToDualNumber Λ l)
      (infAutFiberMkPushforwardHom Λ k l p) :=
  sorry

/-- Restriction-of-scalars `k`-module structure on `Inf(p_{l/k})`. -/
instance instModule_k_infAutResidueChange :
    Module k
      (infinitesimalAutomorphismsAt (residueChangeOver Λ k l p)
        (chosenResidueFiberObj (residueChangeOver Λ k l p))
        (pushforwardObj (residueChangeOver Λ k l p) (residueToDualNumber Λ l)
          (chosenResidueFiberObj (residueChangeOver Λ k l p)))
        (chosenDualNumberHom (residueChangeOver Λ k l p)
          (chosenResidueFiberObj (residueChangeOver Λ k l p)))) :=
  Module.restrictScalars k l _

/-- The `k`-action on `Inf(p_{l/k})` obtained by restriction of scalars is compatible with
the `l`-action. -/
instance instIsScalarTower_infAutResidueChange :
    IsScalarTower k l
      (infinitesimalAutomorphismsAt (residueChangeOver Λ k l p)
        (chosenResidueFiberObj (residueChangeOver Λ k l p))
        (pushforwardObj (residueChangeOver Λ k l p) (residueToDualNumber Λ l)
          (chosenResidueFiberObj (residueChangeOver Λ k l p)))
        (chosenDualNumberHom (residueChangeOver Λ k l p)
          (chosenResidueFiberObj (residueChangeOver Λ k l p)))) :=
  sorry

/-- Right `l`-module structure on `Inf(p) ⊗[k] l`, acting on the second factor. -/
instance instModule_infAutTensor :
    Module l
      (infinitesimalAutomorphismsAt p (chosenResidueFiberObj p)
        (pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))
        (chosenDualNumberHom p (chosenResidueFiberObj p)) ⊗[k] l) where
  smul a x := TensorProduct.map LinearMap.id (LinearMap.mulLeft k a) x
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The canonical `k`-linear comparison `Inf(p) ⟶ Inf(p_{l/k})`, obtained by pushing
automorphisms along the dual-number/square-zero identification, applying `fiberMk`, and
conjugating to the chosen infinitesimal-automorphism space of `p_{l/k}`. -/
def infAutRestrict :
    infinitesimalAutomorphismsAt p (chosenResidueFiberObj p)
        (pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))
        (chosenDualNumberHom p (chosenResidueFiberObj p)) →ₗ[k]
      infinitesimalAutomorphismsAt (residueChangeOver Λ k l p)
        (chosenResidueFiberObj (residueChangeOver Λ k l p))
        (pushforwardObj (residueChangeOver Λ k l p) (residueToDualNumber Λ l)
          (chosenResidueFiberObj (residueChangeOver Λ k l p)))
        (chosenDualNumberHom (residueChangeOver Λ k l p)
          (chosenResidueFiberObj (residueChangeOver Λ k l p))) where
  toFun α :=
    infAutAtCanonicalIso (residueChangeOver Λ k l p)
      (infAutFiberMkPushforwardHom Λ k l p)
      (chosenDualNumberHom (residueChangeOver Λ k l p)
        (chosenResidueFiberObj (residueChangeOver Λ k l p)))
      ⟨mapAut (correspondingDualNumberObj Λ k l p) (fiberMk Λ k l p (dualNumber Λ l))
          (pushforwardAut p (infAutResidueChangeDualNumberHom Λ k l)
            (chosenResidueFiberObj p)
            (pushforwardAut p (infAutSquareZeroHom Λ k l)
              (chosenResidueFiberObj p) α.val)),
        sorry⟩
  map_add' := sorry
  map_smul' := sorry

/-- The underlying automorphism of `infAutRestrict` is conjugation of the
square-zero/`fiberMk` composite along the unique dual-number comparison. -/
theorem infAutRestrict_apply
    (α :
      infinitesimalAutomorphismsAt p (chosenResidueFiberObj p)
        (pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))
        (chosenDualNumberHom p (chosenResidueFiberObj p))) :
    (infAutRestrict Λ k l p α).val =
      (fiberIso_of_fiberIso (residueChangeOver Λ k l p)
          (default : correspondingResidueFiber Λ k l p ≅
            chosenResidueFiberObj (residueChangeOver Λ k l p))
          (infAutFiberMkPushforwardHom Λ k l p)
          (chosenDualNumberHom (residueChangeOver Λ k l p)
            (chosenResidueFiberObj (residueChangeOver Λ k l p)))).conjAut
        (mapAut (correspondingDualNumberObj Λ k l p) (fiberMk Λ k l p (dualNumber Λ l))
          (pushforwardAut p (infAutResidueChangeDualNumberHom Λ k l)
            (chosenResidueFiberObj p)
            (pushforwardAut p (infAutSquareZeroHom Λ k l)
              (chosenResidueFiberObj p) α.val))) :=
  sorry

/-- The bilinear comparison sending `(α, a)` to `a • infAutRestrict α`. -/
def infAutTensorBilin :
    infinitesimalAutomorphismsAt p (chosenResidueFiberObj p)
        (pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))
        (chosenDualNumberHom p (chosenResidueFiberObj p)) →ₗ[k]
      l →ₗ[k]
        infinitesimalAutomorphismsAt (residueChangeOver Λ k l p)
          (chosenResidueFiberObj (residueChangeOver Λ k l p))
          (pushforwardObj (residueChangeOver Λ k l p) (residueToDualNumber Λ l)
            (chosenResidueFiberObj (residueChangeOver Λ k l p)))
          (chosenDualNumberHom (residueChangeOver Λ k l p)
            (chosenResidueFiberObj (residueChangeOver Λ k l p))) :=
  LinearMap.mk₂ k (fun α a ↦ a • infAutRestrict Λ k l p α) sorry sorry sorry sorry

/-- On pairs, `infAutTensorBilin` is scalar multiplication of `infAutRestrict`. -/
theorem infAutTensorBilin_apply
    (α :
      infinitesimalAutomorphismsAt p (chosenResidueFiberObj p)
        (pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))
        (chosenDualNumberHom p (chosenResidueFiberObj p)))
    (a : l) :
    infAutTensorBilin Λ k l p α a = a • infAutRestrict Λ k l p α :=
  sorry

/-- The canonical `l`-linear comparison `Inf(p) ⊗[k] l ⟶ Inf(p_{l/k})`, the scalar
extension of `infAutRestrict`. -/
def infAutTensor :
    infinitesimalAutomorphismsAt p (chosenResidueFiberObj p)
        (pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))
        (chosenDualNumberHom p (chosenResidueFiberObj p)) ⊗[k] l →ₗ[l]
      infinitesimalAutomorphismsAt (residueChangeOver Λ k l p)
        (chosenResidueFiberObj (residueChangeOver Λ k l p))
        (pushforwardObj (residueChangeOver Λ k l p) (residueToDualNumber Λ l)
          (chosenResidueFiberObj (residueChangeOver Λ k l p)))
        (chosenDualNumberHom (residueChangeOver Λ k l p)
          (chosenResidueFiberObj (residueChangeOver Λ k l p))) where
  toFun := ⇑(TensorProduct.lift (infAutTensorBilin Λ k l p))
  map_add' := sorry
  map_smul' := sorry

/-- `infAutTensor` is the `TensorProduct.lift` of `infAutTensorBilin`. -/
theorem infAutTensor_spec
    (x :
      infinitesimalAutomorphismsAt p (chosenResidueFiberObj p)
          (pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))
          (chosenDualNumberHom p (chosenResidueFiberObj p)) ⊗[k]
        l) :
    infAutTensor Λ k l p x = TensorProduct.lift (infAutTensorBilin Λ k l p) x :=
  sorry

/-- On pure tensors, `infAutTensor` sends `α ⊗ₜ a` to `a • infAutRestrict α`. -/
theorem infAutTensor_tmul
    (α :
      infinitesimalAutomorphismsAt p (chosenResidueFiberObj p)
        (pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))
        (chosenDualNumberHom p (chosenResidueFiberObj p)))
    (a : l) :
    infAutTensor Λ k l p (α ⊗ₜ a) = a • infAutRestrict Λ k l p α :=
  sorry

end residueChangeOver

end ArtinianLocalAlgCat
