/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SquareZeroFunctor
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Module
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Predeformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange.Tangent
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange.Residue

/-!
# Residue-change comparison of infinitesimal automorphisms

A finite residue-field extension induces a canonical scalar-extension comparison
of infinitesimal automorphism spaces.
-/

public section

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

namespace residueChangeOver


variable {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)
variable [IsDeformationCategory p]

/-- The object `k → k[ε]` of `Under (residue Λ k)`. -/
private def infAutDualNumberUnder : Under (residue Λ k) :=
  Under.mk (residueToDualNumber Λ k)

/-- The object `k → k[l]` of `Under (residue Λ k)`, after the dual-number/square-zero
identification and scalar extension `Algebra.linearMap k l`. -/
private def infAutSquareZeroUnder : Under (residue Λ k) :=
  Under.mk
    (residueToDualNumber Λ k ≫ (dualNumberIsoSquareZero Λ k).hom ≫
      squareZeroMap (Algebra.linearMap k l))

/-- The object `k → k[lε]` of `Under (residue Λ k)`, after identifying `k[l]` with
residue change of `l[ε]`. -/
private def infAutResidueChangeDualNumberUnder : Under (residue Λ k) :=
  Under.mk
    (residueToDualNumber Λ k ≫ (dualNumberIsoSquareZero Λ k).hom ≫
      squareZeroMap (Algebra.linearMap k l) ≫
        (residueChangeDualNumberIso Λ k l).inv)

/-- The Under-morphism `(k → k[ε]) ⟶ (k → k[l])` induced by
`dualNumberIsoSquareZero.hom ≫ squareZeroMap (Algebra.linearMap k l)`. -/
private def infAutSquareZeroHom : infAutDualNumberUnder Λ k ⟶ infAutSquareZeroUnder Λ k l := by
  refine Under.homMk ((dualNumberIsoSquareZero Λ k).hom ≫ squareZeroMap (Algebra.linearMap k l)) ?_
  sorry

/-- The Under-morphism `(k → k[l]) ⟶ (k → k[lε])` induced by
`residueChangeDualNumberIso.inv`. -/
private def infAutResidueChangeDualNumberHom :
    infAutSquareZeroUnder Λ k l ⟶ infAutResidueChangeDualNumberUnder Λ k l := by
  refine Under.homMk (residueChangeDualNumberIso Λ k l).inv ?_
  sorry

/-- The Under-morphism `(k → l ×_l k) ⟶ (k → k[lε])` induced by residue change of
`residueToDualNumber`. -/
private def infAutCorrespondingHom :
    Under.mk (residueChangeResidueIso Λ k l).inv ⟶ infAutResidueChangeDualNumberUnder Λ k l :=
  Under.homMk ((residueChangeFunctor Λ k l).map (residueToDualNumber Λ l)) sorry

/-- The object of `F(l ×_l k)` corresponding to the chosen residue-fibre object of `p`. -/
private def correspondingResidueObj :
    p.Fiber ((residueChangeFunctor Λ k l).obj (residue Λ l)) :=
  pushforwardObj p (residueChangeResidueIso Λ k l).inv (chosenResidueFiberObj p)

/-- The object of `F(k[lε])` obtained by pushing the chosen residue-fibre object of `p`
along the dual-number/square-zero/residue-change composite. -/
private def correspondingDualNumberObj :
    p.Fiber ((residueChangeFunctor Λ k l).obj (dualNumber Λ l)) :=
  pushforwardObj p (infAutResidueChangeDualNumberUnder Λ k l).hom (chosenResidueFiberObj p)

/-- The object of `F_{l/k}` over `l` corresponding to the chosen residue-fibre object of `p`. -/
private def correspondingResidueFiber :
    (residueChangeOver Λ k l p).Fiber (residue Λ l) :=
  (fiberMk Λ k l p (residue Λ l)).obj (correspondingResidueObj Λ k l p)

/-- The object of `F_{l/k}` over `l[ε]` obtained by `fiberMk` of
`correspondingDualNumberObj`. -/
private def correspondingDualNumberFiber :
    (residueChangeOver Λ k l p).Fiber (dualNumber Λ l) :=
  (fiberMk Λ k l p (dualNumber Λ l)).obj (correspondingDualNumberObj Λ k l p)

/-- The dual-number pushforward of `correspondingResidueFiber` in `F_{l/k}`, as the
pullback morphism with first component `residueToDualNumber` and second component
the selected comparison of the two pushforwards of the chosen residue object. -/
private def infAutFiberMkPushforwardHom :
    fiberInclusion.obj (correspondingResidueFiber Λ k l p) ⟶
      fiberInclusion.obj (correspondingDualNumberFiber Λ k l p) where
  fst := residueToDualNumber Λ l
  snd := pushforwardComparison p (infAutCorrespondingHom Λ k l) (chosenResidueFiberObj p)
  w := sorry

/-- `infAutFiberMkPushforwardHom` lies over `residueToDualNumber`. -/
private instance instIsHomLift_infAutFiberMkPushforwardHom :
    (residueChangeOver Λ k l p).IsHomLift (residueToDualNumber Λ l)
      (infAutFiberMkPushforwardHom Λ k l p) :=
  sorry

/-- `infAutFiberMkPushforwardHom` is strongly cocartesian over `residueToDualNumber`. -/
private instance instIsStronglyCocartesian_infAutFiberMkPushforwardHom :
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
  IsScalarTower.restrictScalars k l _

/-- Right `l`-module structure on `Inf(p) ⊗[k] l`, acting on the second factor. -/
instance instModule_infAutTensor :
    Module l
      (infinitesimalAutomorphismsAt p (chosenResidueFiberObj p)
        (pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))
        (chosenDualNumberHom p (chosenResidueFiberObj p)) ⊗[k] l) := by
  let action := fun (a : l)
      (x : infinitesimalAutomorphismsAt p (chosenResidueFiberObj p)
        (pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))
        (chosenDualNumberHom p (chosenResidueFiberObj p)) ⊗[k] l) =>
    TensorProduct.map LinearMap.id (LinearMap.mulLeft k a) x
  have laws : (∀ x, action 1 x = x) ∧
      (∀ a b x, action (a * b) x = action a (action b x)) ∧
      (∀ a, action a 0 = 0) ∧
      (∀ a x y, action a (x + y) = action a x + action a y) ∧
      (∀ a b x, action (a + b) x = action a x + action b x) ∧
      (∀ x, action 0 x = 0) := by
    sorry
  exact
    { smul := action
      one_smul := laws.1
      mul_smul := laws.2.1
      smul_zero := laws.2.2.1
      smul_add := laws.2.2.2.1
      add_smul := laws.2.2.2.2.1
      zero_smul := laws.2.2.2.2.2 }

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
          (chosenResidueFiberObj (residueChangeOver Λ k l p))) := by
  let f := fun (α :
      infinitesimalAutomorphismsAt p (chosenResidueFiberObj p)
        (pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))
        (chosenDualNumberHom p (chosenResidueFiberObj p))) =>
    infAutAtCanonicalIso (residueChangeOver Λ k l p)
      (infAutFiberMkPushforwardHom Λ k l p)
      (chosenDualNumberHom (residueChangeOver Λ k l p)
        (chosenResidueFiberObj (residueChangeOver Λ k l p)))
      ⟨mapAut (correspondingDualNumberObj Λ k l p) (fiberMk Λ k l p (dualNumber Λ l))
          (pushforwardAut p (infAutResidueChangeDualNumberHom Λ k l)
            (chosenResidueFiberObj p)
            (pushforwardAut p (infAutSquareZeroHom Λ k l)
              (chosenResidueFiberObj p) α.val)),
        by
          rw [infinitesimalAutomorphismsAt_eq_top]
          trivial⟩
  have laws : (∀ α β, f (α + β) = f α + f β) ∧
      (∀ (a : k) α, f (a • α) = a • f α) := by
    sorry
  exact { toFun := f, map_add' := laws.1, map_smul' := laws.2 }

/-- The underlying automorphism of `infAutRestrict` is conjugation of the
square-zero/`fiberMk` composite along the unique dual-number comparison. -/
private theorem infAutRestrict_apply
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
private def infAutTensorBilin :
    infinitesimalAutomorphismsAt p (chosenResidueFiberObj p)
        (pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))
        (chosenDualNumberHom p (chosenResidueFiberObj p)) →ₗ[k]
      l →ₗ[k]
        infinitesimalAutomorphismsAt (residueChangeOver Λ k l p)
          (chosenResidueFiberObj (residueChangeOver Λ k l p))
          (pushforwardObj (residueChangeOver Λ k l p) (residueToDualNumber Λ l)
            (chosenResidueFiberObj (residueChangeOver Λ k l p)))
          (chosenDualNumberHom (residueChangeOver Λ k l p)
            (chosenResidueFiberObj (residueChangeOver Λ k l p))) := by
  let f := fun α (a : l) ↦ a • infAutRestrict Λ k l p α
  have laws : (∀ α β a, f (α + β) a = f α a + f β a) ∧
      (∀ (c : k) α a, f (c • α) a = c • f α a) ∧
      (∀ α a b, f α (a + b) = f α a + f α b) ∧
      (∀ (c : k) α a, f α (c • a) = c • f α a) := by
    sorry
  exact LinearMap.mk₂ k f laws.1 laws.2.1 laws.2.2.1 laws.2.2.2

/-- On pairs, `infAutTensorBilin` is scalar multiplication of `infAutRestrict`. -/
private theorem infAutTensorBilin_apply
    (α :
      infinitesimalAutomorphismsAt p (chosenResidueFiberObj p)
        (pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))
        (chosenDualNumberHom p (chosenResidueFiberObj p)))
    (a : l) :
    infAutTensorBilin Λ k l p α a = a • infAutRestrict Λ k l p α :=
  rfl

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
          (chosenResidueFiberObj (residueChangeOver Λ k l p))) := by
  let f := TensorProduct.lift (infAutTensorBilin Λ k l p)
  have laws : (∀ x y, f (x + y) = f x + f y) ∧
      (∀ (a : l) x, f (a • x) = a • f x) := by
    sorry
  exact { toFun := f, map_add' := laws.1, map_smul' := laws.2 }

/-- `infAutTensor` is the `TensorProduct.lift` of `infAutTensorBilin`. -/
private theorem infAutTensor_spec
    (x :
      infinitesimalAutomorphismsAt p (chosenResidueFiberObj p)
          (pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))
          (chosenDualNumberHom p (chosenResidueFiberObj p)) ⊗[k]
        l) :
    infAutTensor Λ k l p x = TensorProduct.lift (infAutTensorBilin Λ k l p) x :=
  rfl

/-- On pure tensors, `infAutTensor` sends `α ⊗ₜ a` to `a • infAutRestrict α`. -/
theorem infAutTensor_tmul
    (α :
      infinitesimalAutomorphismsAt p (chosenResidueFiberObj p)
        (pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))
        (chosenDualNumberHom p (chosenResidueFiberObj p)))
    (a : l) :
    infAutTensor Λ k l p (α ⊗ₜ a) = a • infAutRestrict Λ k l p α :=
  sorry

/-- The canonical scalar-extension comparison of infinitesimal automorphism spaces
for a deformation category and a finite residue-field extension is bijective. -/
theorem bijective_infAutTensor :
    Function.Bijective (infAutTensor Λ k l p) :=
  sorry

end residueChangeOver

end ArtinianLocalAlgCat
