/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Opposite
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Opposite
public import ReasLib.Algebra.Homology.DifferentialGradedModule.TensorProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction of scalars and relative tensor products

For a cochain-DGA map `φ : CochainDGAlgebra.Hom A B`, imposing the `B`-balancing relations gives a canonical map
from the tensor product of the restricted factors over `A` to their tensor product over `B`.
The left factor is represented universe-polymorphically as a right module over `B.opposite`.
-/

@[expose] public section

noncomputable section

universe u x y v w

open CategoryTheory
open scoped TensorProduct

namespace DifferentialGradedModule.TensorProduct

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R} {B : CochainDGAlgebra.{u, y} R}

/-- The homogeneous pairing from the two restricted factors to their relative tensor product
over the target DGA. -/
def restrictPairing (φ : CochainDGAlgebra.Hom A B)
    (M : DifferentialGradedModule.{u, v} B)
    (N : DifferentialGradedModule.{u, w} B.opposite) :
    Pairing (φ.restrictModule M)
      (LeftDifferentialGradedModule.unop (φ.opposite.restrictModule N))
      (complex M (LeftDifferentialGradedModule.unop N)) :=
  fun _ _ ↦ ModuleCat.TensorProduct.lift R
    (LinearMap.mk₂ R
      (fun m n ↦ tmul M (LeftDifferentialGradedModule.unop N) m n)
      (fun m m' n ↦ (tmulLeft M (LeftDifferentialGradedModule.unop N) n).map_add m m')
      (fun r m n ↦ (tmulLeft M (LeftDifferentialGradedModule.unop N) n).map_smul r m)
      (fun m n n' ↦ (tmulRight M (LeftDifferentialGradedModule.unop N) m).map_add n n')
      (fun r m n ↦ (tmulRight M (LeftDifferentialGradedModule.unop N) m).map_smul r n))

/-- The restriction pairing evaluates as the pure tensor class over the target DGA. -/
@[simp]
theorem restrictPairing_apply (φ : CochainDGAlgebra.Hom A B)
    (M : DifferentialGradedModule.{u, v} B)
    (N : DifferentialGradedModule.{u, w} B.opposite)
    (p q : ℤ) (m : M.X p) (n : N.X q) :
    restrictPairing φ M N p q (m ⊗ₜ[R] n) =
      tmul M (LeftDifferentialGradedModule.unop N) m n := by
  rfl

/-- The restriction pairing is balanced over the source DGA. -/
theorem restrictPairing_isBalanced (φ : CochainDGAlgebra.Hom A B)
    (M : DifferentialGradedModule.{u, v} B)
    (N : DifferentialGradedModule.{u, w} B.opposite) :
    IsBalanced (φ.restrictModule M)
      (LeftDifferentialGradedModule.unop (φ.opposite.restrictModule N))
      (restrictPairing φ M N) := by
  intro p i q m a n
  exact tmul_smul M (LeftDifferentialGradedModule.unop N) p i q m (φ i a) n

/-- The restriction pairing commutes with the total differentials. -/
theorem restrictPairing_isDifferentialCompatible (φ : CochainDGAlgebra.Hom A B)
    (M : DifferentialGradedModule.{u, v} B)
    (N : DifferentialGradedModule.{u, w} B.opposite) :
    IsDifferentialCompatible (φ.restrictModule M)
      (LeftDifferentialGradedModule.unop (φ.opposite.restrictModule N))
      (restrictPairing φ M N) := by
  intro p q m n
  exact d_tmul M (LeftDifferentialGradedModule.unop N) p q m n

/-- The canonical comparison
`Res M ⊗_A Res N ⟶ M ⊗_B N` obtained by imposing the additional `B`-balancing relations. -/
@[stacks 0GZI "restriction comparison for relative tensor products"]
def restrictMap (φ : CochainDGAlgebra.Hom A B)
    (M : DifferentialGradedModule.{u, v} B)
    (N : DifferentialGradedModule.{u, w} B.opposite) :
    complex (φ.restrictModule M)
        (LeftDifferentialGradedModule.unop (φ.opposite.restrictModule N)) ⟶
      complex M (LeftDifferentialGradedModule.unop N) :=
  lift (φ.restrictModule M)
    (LeftDifferentialGradedModule.unop (φ.opposite.restrictModule N))
    (restrictPairing φ M N) (restrictPairing_isBalanced φ M N)
    (restrictPairing_isDifferentialCompatible φ M N)

/-- The restriction comparison sends a restricted pure tensor to the same pure tensor class over
the target DGA. -/
@[simp]
theorem restrictMap_tmul (φ : CochainDGAlgebra.Hom A B)
    (M : DifferentialGradedModule.{u, v} B)
    (N : DifferentialGradedModule.{u, w} B.opposite)
    (p q : ℤ) (m : M.X p) (n : N.X q) :
    (restrictMap φ M N).f (p + q)
        (tmul (φ.restrictModule M)
          (LeftDifferentialGradedModule.unop (φ.opposite.restrictModule N)) m n) =
      tmul M (LeftDifferentialGradedModule.unop N) m n := by
  rw [restrictMap, lift_tmul, restrictPairing_apply]

/-- The restriction comparison is natural in the right-module factor. -/
theorem mapRight_restrictMap (φ : CochainDGAlgebra.Hom A B)
    {M M' : DifferentialGradedModule.{u, v} B} (f : M ⟶ M')
    (N : DifferentialGradedModule.{u, w} B.opposite) :
    mapRight (LeftDifferentialGradedModule.unop (φ.opposite.restrictModule N))
          (φ.restrictHom f) ≫
        restrictMap φ M' N =
      restrictMap φ M N ≫
        mapRight (LeftDifferentialGradedModule.unop N) f := by
  apply hom_ext (φ.restrictModule M)
    (LeftDifferentialGradedModule.unop (φ.opposite.restrictModule N))
  intro p q m n
  change (restrictMap φ M' N).f (p + q)
      ((mapRight _ (φ.restrictHom f)).f (p + q) (tmul _ _ m n)) =
    (mapRight _ f).f (p + q)
      ((restrictMap φ M N).f (p + q) (tmul _ _ m n))
  rw [mapRight_tmul, restrictMap_tmul, restrictMap_tmul, mapRight_tmul]
  rfl

/-- The restriction comparison is natural in the left-module factor represented over the
opposite DGA. -/
theorem mapLeft_restrictMap (φ : CochainDGAlgebra.Hom A B)
    (M : DifferentialGradedModule.{u, v} B)
    {N N' : DifferentialGradedModule.{u, w} B.opposite} (g : N ⟶ N') :
    mapLeft (φ.restrictModule M)
          ((LeftDifferentialGradedModule.unopFunctor A).map
            (φ.opposite.restrictHom g)) ≫
        restrictMap φ M N' =
      restrictMap φ M N ≫
        mapLeft M ((LeftDifferentialGradedModule.unopFunctor B).map g) := by
  apply hom_ext (φ.restrictModule M)
    (LeftDifferentialGradedModule.unop (φ.opposite.restrictModule N))
  intro p q m n
  change (restrictMap φ M N').f (p + q)
      ((mapLeft _ _).f (p + q) (tmul _ _ m n)) =
    (mapLeft _ _).f (p + q)
      ((restrictMap φ M N).f (p + q) (tmul _ _ m n))
  rw [mapLeft_tmul, restrictMap_tmul, restrictMap_tmul, mapLeft_tmul]
  rfl

/-- Relative tensor after restricting both inputs along `φ`, as a curried bifunctor on right
modules over `B` and `B.opposite`. -/
def restrictedFunctor (φ : CochainDGAlgebra.Hom A B) :
    DifferentialGradedModule.{u, v} B ⥤
      DifferentialGradedModule.{u, w} B.opposite ⥤
        CochainComplex (ModuleCat.{max v w} R) ℤ where
  obj M := φ.opposite.restrictFunctor ⋙
    LeftDifferentialGradedModule.unopFunctor A ⋙
      leftModuleFunctor (φ.restrictModule M)
  map {M M'} f :=
    { app := fun N ↦ mapRight
        (LeftDifferentialGradedModule.unop (φ.opposite.restrictModule N))
        (φ.restrictHom f)
      naturality := by
        intro N N' g
        apply hom_ext (φ.restrictModule M)
          (LeftDifferentialGradedModule.unop (φ.opposite.restrictModule N))
        intro p q m n
        change (mapRight _ (φ.restrictHom f)).f (p + q)
            ((mapLeft _ _).f (p + q) (tmul _ _ m n)) =
          (mapLeft _ _).f (p + q)
            ((mapRight _ (φ.restrictHom f)).f (p + q) (tmul _ _ m n))
        rw [mapLeft_tmul, mapRight_tmul, mapRight_tmul, mapLeft_tmul] }
  map_id := by
    intro M
    apply NatTrans.ext
    funext N
    apply hom_ext (φ.restrictModule M)
      (LeftDifferentialGradedModule.unop (φ.opposite.restrictModule N))
    intro p q m n
    change (mapRight _ (φ.restrictHom (𝟙 M))).f (p + q) (tmul _ _ m n) = _
    rw [mapRight_tmul]
    rfl
  map_comp := by
    intro M M' M'' f g
    apply NatTrans.ext
    funext N
    apply hom_ext (φ.restrictModule M)
      (LeftDifferentialGradedModule.unop (φ.opposite.restrictModule N))
    intro p q m n
    change (mapRight _ (φ.restrictHom (f ≫ g))).f (p + q) (tmul _ _ m n) =
      (mapRight _ (φ.restrictHom g)).f (p + q)
        ((mapRight _ (φ.restrictHom f)).f (p + q) (tmul _ _ m n))
    rw [mapRight_tmul, mapRight_tmul, mapRight_tmul]
    rfl

/-- Relative tensor over `B`, with the left module represented as a right module over
`B.opposite`. -/
def oppositeFunctor (B : CochainDGAlgebra.{u, y} R) :
    DifferentialGradedModule.{u, v} B ⥤
      DifferentialGradedModule.{u, w} B.opposite ⥤
        CochainComplex (ModuleCat.{max v w} R) ℤ where
  obj M := LeftDifferentialGradedModule.unopFunctor B ⋙ leftModuleFunctor M
  map {M M'} f :=
    { app := fun N ↦ mapRight (LeftDifferentialGradedModule.unop N) f
      naturality := by
        intro N N' g
        apply hom_ext M (LeftDifferentialGradedModule.unop N)
        intro p q m n
        change (mapRight _ f).f (p + q)
            ((mapLeft _ _).f (p + q) (tmul _ _ m n)) =
          (mapLeft _ _).f (p + q)
            ((mapRight _ f).f (p + q) (tmul _ _ m n))
        rw [mapLeft_tmul, mapRight_tmul, mapRight_tmul, mapLeft_tmul] }
  map_id := by
    intro M
    apply NatTrans.ext
    funext N
    exact (rightModuleFunctor (LeftDifferentialGradedModule.unop N)).map_id M
  map_comp := by
    intro M M' M'' f g
    apply NatTrans.ext
    funext N
    exact (rightModuleFunctor (LeftDifferentialGradedModule.unop N)).map_comp f g

-- Comparing the nested functor projections uses about 807000 heartbeats, measured with
-- `#count_heartbeats` on the declaration below.
set_option maxHeartbeats 1600000 in
/-- The restriction comparisons assemble into a natural transformation between the two
curried relative tensor bifunctors. -/
@[stacks 0GZI "naturality of restriction comparison for relative tensor"]
def restrictNatTrans (φ : CochainDGAlgebra.Hom A B) :
    restrictedFunctor φ ⟶ oppositeFunctor B where
  app M :=
    { app := fun N ↦ restrictMap φ M N
      naturality := by
        intro N N' g
        exact mapLeft_restrictMap φ M g }
  naturality := by
    intro M M' f
    apply NatTrans.ext
    funext N
    change mapRight
          (LeftDifferentialGradedModule.unop (φ.opposite.restrictModule N))
          (φ.restrictHom f) ≫ restrictMap φ M' N =
      restrictMap φ M N ≫ mapRight (LeftDifferentialGradedModule.unop N) f
    exact mapRight_restrictMap φ f N

end DifferentialGradedModule.TensorProduct
