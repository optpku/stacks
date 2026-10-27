/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.CategoryTheory.Fibered.HomPresheaf.Isom
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic

/-!
# Isomorphism algebraic spaces of an algebraic stack

For fibre objects `x, y` of an algebraic stack `X` over a scheme `T`, the
isomorphism presheaf `Isom_X(x, y)` is transported along the iterated slice
equivalence to an algebraic space over `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Functor
open FiberedCategoryOver.Groupoids
open scoped CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Isom

/-- The scheme `T` viewed as an algebraic space over itself. -/
abbrev selfSpace {S : Scheme.{u}} (T : Over S) : AlgebraicSpace T.left :=
  AlgebraicSpace.ofOver (Over.mk (𝟙 T.left))

/-- The isomorphism presheaf `Isom_X(x, y)` on schemes over `T`. -/
def isomOverLeft {S : Scheme.{u}} {X : GroupoidsOver S} {T : Over S}
    (x y : X.p.Fiber T) : (Over T.left)ᵒᵖ ⥤ Type u :=
  T.iteratedSliceEquiv.inverse.op ⋙ Functor.isomorphismPresheaf X.p x y

/-- `isomOverLeft x y` is the slice transport of `Functor.isomorphismPresheaf X.p x y`. -/
theorem isomOverLeft_eq {S : Scheme.{u}} {X : GroupoidsOver S} {T : Over S}
    (x y : X.p.Fiber T) :
    isomOverLeft x y =
      T.iteratedSliceEquiv.inverse.op ⋙ Functor.isomorphismPresheaf X.p x y :=
  rfl

/-- Universe-raised comparison of `isomOverLeft` with the `ULift` isomorphism presheaf. -/
def isomOverLeft_uliftIso {S : Scheme.{u}} {X : GroupoidsOver S} {T : Over S}
    (x y : X.p.Fiber T) :
    isomOverLeft x y ⋙ uliftFunctor.{u + 1, u} ≅
      T.iteratedSliceEquiv.inverse.op ⋙ Functor.isomorphismPresheafULift X.p x y :=
  Iso.refl _

/-- A vertical arrow is invertible by the Cartesian universal property. -/
private theorem fiberHom_isIso {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Over S} {a b : X.p.Fiber U} (φ : a ⟶ b) : IsIso φ := by
  let cartesianAt : ∀ {R T : Over S} {c d : X.total} (f : R ⟶ T) (g : c ⟶ d),
      X.p.IsHomLift f g → X.p.IsCartesian f g := by
    intro R T c d f g h
    cases h
    exact Functor.IsFibered.InGroupoids.all_isCartesian g
  letI : X.p.IsHomLift (𝟙 U) φ.val := φ.property
  letI : X.p.IsCartesian (𝟙 U) φ.val := cartesianAt _ _ φ.property
  letI : X.p.IsHomLift (𝟙 U) (𝟙 b.val) := IsHomLift.id b.property
  let e := Functor.IsCartesian.domainUniqueUpToIso X.p (𝟙 U) (𝟙 b.val) φ.val
  have he : e.hom = φ.val := by
    exact (Category.comp_id _).symm.trans
      (Functor.IsCartesian.fac X.p (𝟙 U) (𝟙 b.val) φ.val)
  letI : IsIso φ.val := he ▸ e.isIso_hom
  refine ⟨⟨⟨inv φ.val, IsHomLift.lift_id_inv_isIso X.p U φ.val⟩, ?_, ?_⟩⟩
  · apply Subtype.ext
    exact IsIso.hom_inv_id φ.val
  · apply Subtype.ext
    exact IsIso.inv_hom_id φ.val

/-- The transported isomorphism presheaf is an fppf sheaf whenever the fibre
pseudofunctor is a prestack. -/
theorem isomOverLeft_isSheaf {S : Scheme.{u}} {X : GroupoidsOver S}
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor X.p) (Scheme.fppfTopology.over S)]
    {T : Over S} (x y : X.p.Fiber T) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over T.left) (isomOverLeft x y) := by
  let F := Functor.fiberPseudofunctor X.p
  have htop : Pseudofunctor.isomSubpresheaf F x y = ⊤ := by
    ext W φ
    change IsIso φ ↔ True
    exact iff_true_intro (fiberHom_isIso φ)
  have hSheaf : Presheaf.IsSheaf ((Scheme.fppfTopology.over S).over T)
      (Functor.isomorphismPresheaf X.p x y) := by
    change Presheaf.IsSheaf _ (Pseudofunctor.isomSubpresheaf F x y).toFunctor
    rw [htop]
    exact (Presheaf.isSheaf_of_iso_iff
      (asIso (Subfunctor.ι (⊤ : Subfunctor (F.presheafHom x y))))).mpr
        (Pseudofunctor.IsPrestack.isSheaf _ _ _)
  exact T.iteratedSliceEquiv.inverse.op_comp_isSheaf_of_isSheaf _ _ _ hSheaf

/-- The algebraic space over `T` representing `Isom_X(x, y)`. -/
def isomSpace {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (x y : X.p.Fiber T) : AlgebraicSpace T.left :=
  AlgebraicSpace.ofFunctor (isomOverLeft x y) (by
    letI : Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor X.p)
        (Scheme.fppfTopology.over S) :=
      (AlgebraicStack.isStack (X := X)).toIsStack.toIsPrestack
    exact isomOverLeft_isSheaf x y) sorry sorry

/-- The functor of points of `isomSpace x y` is `isomOverLeft x y`. -/
theorem isomSpace_functorOfPoints {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {T : Over S} (x y : X.p.Fiber T) :
    (isomSpace x y).functorOfPoints = isomOverLeft x y :=
  rfl

/-- The unique structure morphism from `Isom_X(x, y)` to `T` as an algebraic
space over itself. -/
def isomOverHom {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (x y : X.p.Fiber T) :
    isomSpace x y ⟶ selfSpace T where
  app W := ↾fun _ ↦ Over.homMk W.unop.hom
  naturality := by
    intro W W' f
    ext s
    apply Over.OverMorphism.ext
    exact (Over.w f.unop).symm

/-- Evaluating `isomOverHom x y` at a test scheme returns the unique morphism
to `T`. -/
theorem isomOverHom_app {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {T : Over S} (x y : X.p.Fiber T) (W : (Over T.left)ᵒᵖ)
    (s : (isomSpace x y).functorOfPoints.obj W) :
    (isomOverHom x y).app W s = Over.homMk W.unop.hom :=
  rfl

/-- `Isom_X(x, y)` as an algebraic space over `T`, with unique structure morphism
to `T`. -/
def isomOver {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (x y : X.p.Fiber T) : Over (selfSpace T) :=
  Over.mk (isomOverHom x y)

/-- The underlying algebraic space of `isomOver x y` is `isomSpace x y`. -/
theorem isomOver_left {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (x y : X.p.Fiber T) :
    (isomOver x y).left = isomSpace x y :=
  rfl

/-- The structure morphism of `isomOver x y` is `isomOverHom x y`. -/
theorem isomOver_hom {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (x y : X.p.Fiber T) :
    (isomOver x y).hom = isomOverHom x y :=
  rfl

end AlgebraicGeometry.AlgebraicStack.Isom
