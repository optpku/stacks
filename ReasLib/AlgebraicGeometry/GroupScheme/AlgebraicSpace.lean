/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization.Tensor

/-! # Realization of group schemes as group algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupScheme

variable {S : Scheme.{u}}

open AlgebraicSpace.SchemeRealization

-- Evaluate the realization on scheme-valued points to use the original group laws.
private theorem realization_toBase_unique {X : AlgebraicSpace S}
    (f g : X ⟶ AlgebraicSpace.ofOver (Over.mk (𝟙 S))) : f = g := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro x
  exact Over.mkIdTerminal.hom_ext _ _

private theorem realization_point_eq {U : Over S} {T : (Over S)ᵒᵖ}
    (p : (AlgebraicSpace.ofOver U).functorOfPoints.obj T) : ofOverPoint p = p :=
  yonedaEquiv.apply_symm_apply p

private theorem realization_point_ext {U : Over S} {T : (Over S)ᵒᵖ}
    {p q : (AlgebraicSpace.ofOver U).functorOfPoints.obj T}
    (h : ofOverPoint p = ofOverPoint q) : p = q :=
  (realization_point_eq p).symm.trans (h.trans (realization_point_eq q))

private theorem realization_one_app (G : GroupScheme S) {T : (Over S)ᵒᵖ}
    (p : T.unop ⟶ Over.mk (𝟙 S)) :
    (ofOverMap η[G.X]).app T p = (1 : T.unop ⟶ G.X) := by
  change p ≫ η[G.X] = toUnit T.unop ≫ η[G.X]
  congr 1
  exact toUnit_unique _ _

private theorem realization_inv_point (G : GroupScheme S) {T : (Over S)ᵒᵖ}
    (p : (AlgebraicSpace.ofOver G.X).functorOfPoints.obj T) :
    ofOverPoint ((ofOverMap ι[G.X]).app T p) = (ofOverPoint p)⁻¹ := by
  rw [realization_point_eq, realization_point_eq]
  rfl

private theorem realization_mul_app (G : GroupScheme S) {T : (Over S)ᵒᵖ}
    (p : ((ofOverSlice S).obj G.X ⊗ (ofOverSlice S).obj G.X).left.functorOfPoints.obj T) :
    (sliceTensorComparison G.X G.X ≫ ofOverMap μ[G.X]).app T p =
      ofOverPoint ((fst ((ofOverSlice S).obj G.X) ((ofOverSlice S).obj G.X)).left.app T p) *
        ofOverPoint ((snd ((ofOverSlice S).obj G.X) ((ofOverSlice S).obj G.X)).left.app T p) := by
  change (ofOverMap μ[G.X]).app T ((ofOverMap (lift
    (ofOverPoint ((fst ((ofOverSlice S).obj G.X) ((ofOverSlice S).obj G.X)).left.app T p))
    (ofOverPoint ((snd ((ofOverSlice S).obj G.X) ((ofOverSlice S).obj G.X)).left.app T p)))).app T
      (ofOverIdPoint T.unop)) = _
  dsimp [ofOverMap]
  rw [yoneda_map_app]
  rfl

private theorem realization_mul_comp_point (G : GroupScheme S)
    {X : Over (AlgebraicSpace.ofOver (Over.mk (𝟙 S)))}
    (f : X ⟶ (ofOverSlice S).obj G.X ⊗ (ofOverSlice S).obj G.X)
    (T : (Over S)ᵒᵖ) (x : X.left.functorOfPoints.obj T) :
    ofOverPoint ((f ≫ (Over.homMk (sliceTensorComparison G.X G.X ≫ ofOverMap μ[G.X])
      (realization_toBase_unique _ _) :
        (ofOverSlice S).obj G.X ⊗ (ofOverSlice S).obj G.X ⟶ (ofOverSlice S).obj G.X)).left.app T x) =
      ofOverPoint ((f ≫ fst ((ofOverSlice S).obj G.X) ((ofOverSlice S).obj G.X)).left.app T x) *
        ofOverPoint ((f ≫ snd ((ofOverSlice S).obj G.X) ((ofOverSlice S).obj G.X)).left.app T x) :=
  (realization_point_eq _).trans (realization_mul_app G (f.left.app T x))

private theorem realization_one_comp_point (G : GroupScheme S)
    {X : Over (AlgebraicSpace.ofOver (Over.mk (𝟙 S)))}
    (f : X ⟶ 𝟙_ (Over (AlgebraicSpace.ofOver (Over.mk (𝟙 S)))))
    (T : (Over S)ᵒᵖ) (x : X.left.functorOfPoints.obj T) :
    ofOverPoint ((f ≫ (Over.homMk (ofOverMap η[G.X]) (realization_toBase_unique _ _) :
      𝟙_ (Over (AlgebraicSpace.ofOver (Over.mk (𝟙 S)))) ⟶ (ofOverSlice S).obj G.X)).left.app T x) =
        (1 : T.unop ⟶ G.X) :=
  (realization_point_eq _).trans (realization_one_app G _)

/-- The group algebraic space over `S` associated to a group scheme `G` over `S`.
The underlying object is `ofOver` of `G.X`, and the structure maps are `ofOverMap`
of the scheme-level group operations. -/
def toGroupAlgebraicSpace (G : GroupScheme S) :
    GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk (𝟙 S))) where
  X := (AlgebraicSpace.SchemeRealization.ofOverSlice S).obj G.X
  grp :=
    { one := Over.homMk (AlgebraicSpace.SchemeRealization.ofOverMap η[G.X]) (by
        exact realization_toBase_unique _ _)
      mul := Over.homMk
        (AlgebraicSpace.SchemeRealization.sliceTensorComparison G.X G.X ≫ AlgebraicSpace.SchemeRealization.ofOverMap μ[G.X]) (by
          exact realization_toBase_unique _ _)
      inv := Over.homMk (AlgebraicSpace.SchemeRealization.ofOverMap ι[G.X]) (by
        exact realization_toBase_unique _ _)
      one_mul := by
        apply Over.OverMorphism.ext
        apply NatTrans.ext
        funext T
        apply ConcreteCategory.hom_ext
        intro x
        apply realization_point_ext
        rw [realization_mul_comp_point]
        simp only [whiskerRight_fst, whiskerRight_snd, leftUnitor_hom]
        rw [realization_one_comp_point, one_mul]
      mul_one := by
        apply Over.OverMorphism.ext
        apply NatTrans.ext
        funext T
        apply ConcreteCategory.hom_ext
        intro x
        apply realization_point_ext
        rw [realization_mul_comp_point]
        simp only [whiskerLeft_fst, whiskerLeft_snd, rightUnitor_hom]
        rw [realization_one_comp_point, mul_one]
      mul_assoc := by
        apply Over.OverMorphism.ext
        apply NatTrans.ext
        funext T
        apply ConcreteCategory.hom_ext
        intro x
        apply realization_point_ext
        simp only [← Category.assoc, realization_mul_comp_point]
        simp only [Category.assoc, whiskerRight_fst, whiskerRight_snd,
          whiskerLeft_fst, whiskerLeft_snd]
        simp only [← Category.assoc, realization_mul_comp_point]
        simp only [Category.assoc, associator_hom_fst,
          associator_hom_snd_fst, associator_hom_snd_snd]
        exact mul_assoc _ _ _
      left_inv := by
        apply Over.OverMorphism.ext
        apply NatTrans.ext
        funext T
        apply ConcreteCategory.hom_ext
        intro x
        apply realization_point_ext
        simp only [realization_mul_comp_point, lift_fst, lift_snd,
          realization_one_comp_point]
        change ofOverPoint ((ofOverMap ι[G.X]).app T x) * ofOverPoint x = 1
        rw [realization_inv_point]
        exact inv_mul_cancel _
      right_inv := by
        apply Over.OverMorphism.ext
        apply NatTrans.ext
        funext T
        apply ConcreteCategory.hom_ext
        intro x
        apply realization_point_ext
        simp only [realization_mul_comp_point, lift_fst, lift_snd,
          realization_one_comp_point]
        change ofOverPoint x * ofOverPoint ((ofOverMap ι[G.X]).app T x) = 1
        rw [realization_inv_point]
        exact mul_inv_cancel _ }

/-- The underlying slice object of `toGroupAlgebraicSpace G` is `ofOver` of `G.X`
over `S` as an algebraic space. -/
theorem toGroupAlgebraicSpace_X (G : GroupScheme S) :
    (toGroupAlgebraicSpace G).X = (AlgebraicSpace.SchemeRealization.ofOverSlice S).obj G.X := rfl

/-- The underlying algebraic space of `toGroupAlgebraicSpace G` is `ofOver G.X`. -/
theorem toGroupAlgebraicSpace_left (G : GroupScheme S) :
    (toGroupAlgebraicSpace G).X.left = AlgebraicSpace.ofOver G.X := rfl

end AlgebraicGeometry.GroupScheme
