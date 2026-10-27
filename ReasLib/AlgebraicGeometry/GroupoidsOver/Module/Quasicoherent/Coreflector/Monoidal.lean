/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Monoidal
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector.FlatRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.FlatCover

/-! # Symmetric monoidal quasi-coherent coreflection -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open FiberedCategoryOver.Groupoids Functor.Fiber

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The north-west arrow of the tensor triangle: the tensor of adjunction
counits `ε_F ⊗ ε_G`. -/
def LQCohFbc.tensorCounit {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X) :
    LQCohFbc.tensor
        ((QCoh.toLQCohFbc X).obj ((LQCohFbc.toQCoh X).obj F))
        ((QCoh.toLQCohFbc X).obj ((LQCohFbc.toQCoh X).obj G)) ⟶
      LQCohFbc.tensor F G :=
  LQCohFbc.tensorHom (adj.counit.app F) (adj.counit.app G)

/-- `tensorCounit` is the tensor of the two counit components. -/
theorem LQCohFbc.tensorCounit_eq {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X) :
    LQCohFbc.tensorCounit adj F G =
      LQCohFbc.tensorHom (adj.counit.app F) (adj.counit.app G) :=
  rfl

/-- The composite `i(QF ⊗ QG) ⟶ i(QF) ⊗ i(QG) ⟶ F ⊗ G`, obtained by
descending the explicit presheaf map to the fppf-sheaf target, then applying
`ε_F ⊗ ε_G`. -/
def LQCohFbc.toQCoh_μ_pre {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X) :
    (QCoh.toLQCohFbc X).obj
        (QCoh.Fppf.tensor ((LQCohFbc.toQCoh X).obj F) ((LQCohFbc.toQCoh X).obj G)) ⟶
      LQCohFbc.tensor F G :=
  QCoh.toLQCohFbc_tensoratorOplax ((LQCohFbc.toQCoh X).obj F)
      ((LQCohFbc.toQCoh X).obj G) ≫
    LQCohFbc.tensorCounit adj F G

/-- `toQCoh_μ_pre` is the explicit oplax tensorator, then `ε_F ⊗ ε_G`. -/
theorem LQCohFbc.toQCoh_μ_pre_eq {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X) :
    LQCohFbc.toQCoh_μ_pre adj F G =
      QCoh.toLQCohFbc_tensoratorOplax ((LQCohFbc.toQCoh X).obj F)
          ((LQCohFbc.toQCoh X).obj G) ≫
        LQCohFbc.tensorCounit adj F G :=
  rfl

/-- The tensorator `μ : Q(F) ⊗ Q(G) ⟶ Q(F ⊗ G)` of `Q = LQCohFbc.toQCoh`, as
the adjunct of `ε_F ⊗ ε_G`. The lax i-tensorator identifies the source of
that counit tensor with the inclusion of the quasi-coherent tensor. -/
def LQCohFbc.toQCoh_μ {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X) :
    QCoh.Fppf.tensor ((LQCohFbc.toQCoh X).obj F) ((LQCohFbc.toQCoh X).obj G) ⟶
      (LQCohFbc.toQCoh X).obj (LQCohFbc.tensor F G) :=
  (adj.homEquiv _ _) (LQCohFbc.toQCoh_μ_pre adj F G)

/-- `toQCoh_μ` is the adjunct of `toQCoh_μ_pre`. -/
theorem LQCohFbc.toQCoh_μ_eq {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X) :
    LQCohFbc.toQCoh_μ adj F G =
      (adj.homEquiv _ _) (LQCohFbc.toQCoh_μ_pre adj F G) :=
  rfl

/-- Restriction of a quasi-coherent morphism to the small étale site of an
object of `X`, as `toLQCohFbc` followed by étale inclusion and small-étale
restriction. -/
def QCoh.restrictToSmallEtaleViaRestriction (X : GroupoidsOver S)
    [AlgebraicStack X] (x : X.total) :
    QCoh X ⥤
      RingedSite.ModuleCat.{u}
        (Scheme.Etale.Small.ringedSite (X.p.obj x).left) :=
  QCoh.toLQCohFbc X ⋙ LQCohFbc.inclusion X ⋙ restrictModulesToSmallEtale X x

/-- `restrictToSmallEtaleViaRestriction` is `toLQCohFbc`, then étale inclusion,
then small-étale restriction. -/
theorem QCoh.restrictToSmallEtaleViaRestriction_eq (X : GroupoidsOver S)
    [AlgebraicStack X] (x : X.total) :
    QCoh.restrictToSmallEtaleViaRestriction X x =
      QCoh.toLQCohFbc X ⋙ LQCohFbc.inclusion X ⋙
        restrictModulesToSmallEtale X x :=
  rfl


/-- The adjunct of the tensor of counits is invertible. -/
instance LQCohFbc.toQCoh_μ_isIso {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X) :
    IsIso (LQCohFbc.toQCoh_μ adj F G) :=
  sorry

/-- Characterisation of `μ` by the counit triangle
`i(μ) ≫ ε_{F ⊗ G} = (oplax i-tensorator) ≫ (ε_F ⊗ ε_G)`. -/
theorem LQCohFbc.toQCoh_μ_counit_triangle {X : GroupoidsOver S}
    [AlgebraicStack X] (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X)
    (F G : LQCohFbc X) :
    (QCoh.toLQCohFbc X).map (LQCohFbc.toQCoh_μ adj F G) ≫
        adj.counit.app (LQCohFbc.tensor F G) =
      LQCohFbc.toQCoh_μ_pre adj F G :=
  by
    exact (adj.homEquiv _ _).symm_apply_apply (LQCohFbc.toQCoh_μ_pre adj F G)

/-- Restriction of the i-tensorator `i(QF) ⊗ i(QG) ⟶ i(QF ⊗ QG)` to the small
étale site of a flat object is an isomorphism. -/
theorem QCoh.toLQCohFbc_tensorator_restrictToSmallEtale_isIso
    {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (x : X.p.Fiber U) [AlgebraicStack.Flat (YonedaSlice.representative x)]
    (F G : QCoh X) :
    IsIso
      ((restrictModulesToSmallEtale X (fiberInclusion.obj x)).map
        (QCoh.toLQCohFbc_tensorator_hom F G)) :=
  ((restrictModulesToSmallEtale X (fiberInclusion.obj x)).mapIso
    ((LQCohFbc.inclusion X).mapIso (QCoh.toLQCohFbc_tensorIso F G))).isIso_hom

/-- Restriction of `ε_F ⊗ ε_G` to the small étale site of a flat object is an
isomorphism. -/
theorem LQCohFbc.tensorCounit_restrictToSmallEtale_isIso
    {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (x : X.p.Fiber U) [AlgebraicStack.Flat (YonedaSlice.representative x)]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X) :
    IsIso
      ((restrictModulesToSmallEtale X (fiberInclusion.obj x)).map
        ((LQCohFbc.inclusion X).map (LQCohFbc.tensorCounit adj F G))) :=
  sorry

/-- Restriction of `μ` to the small étale site of a flat object is an
isomorphism. -/
theorem LQCohFbc.toQCoh_μ_restrictToSmallEtale_isIso
    {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (x : X.p.Fiber U) [AlgebraicStack.Flat (YonedaSlice.representative x)]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X) :
    IsIso
      ((QCoh.restrictToSmallEtaleViaRestriction X
          (fiberInclusion.obj x)).map
        (LQCohFbc.toQCoh_μ adj F G)) :=
  sorry


namespace LQCohFbc

/-- The quasi-coherent coreflector has the lax structure of the specified right adjoint. -/
instance toQCoh_laxMonoidal (X : GroupoidsOver S) [AlgebraicStack X] :
    (toQCoh X).LaxMonoidal := (QCoh.toLQCohFbcAdjunction X).rightAdjointLaxMonoidal

/-- The right-adjoint tensorator is the adjunct of the prescribed tensor of counits. -/
theorem toQCoh_laxMonoidal_μ (X : GroupoidsOver S) [AlgebraicStack X]
    (F G : LQCohFbc X) :
    Functor.LaxMonoidal.μ (toQCoh X) F G = toQCoh_μ (QCoh.toLQCohFbcAdjunction X) F G := rfl

/-- The right-adjoint unit comparison is invertible. -/
instance toQCoh_unit_isIso (X : GroupoidsOver S) [AlgebraicStack X] :
    IsIso (Functor.LaxMonoidal.ε (toQCoh X)) := sorry

/-- The canonical right-adjoint tensor comparison is invertible. -/
instance toQCoh_tensorator_isIso (X : GroupoidsOver S) [AlgebraicStack X]
    (F G : LQCohFbc X) : IsIso (Functor.LaxMonoidal.μ (toQCoh X) F G) :=
  toQCoh_μ_isIso (QCoh.toLQCohFbcAdjunction X) F G

/-- Quasi-coherent coreflection preserves the tensor unit and tensor products strongly. -/
instance toQCoh_monoidal (X : GroupoidsOver S) [AlgebraicStack X] :
    (toQCoh X).Monoidal := Functor.Monoidal.ofLaxMonoidal (toQCoh X)

/-- Quasi-coherent coreflection preserves the symmetry of module tensors. -/
instance toQCoh_braided (X : GroupoidsOver S) [AlgebraicStack X] :
    (toQCoh X).Braided where
  braided := sorry

end LQCohFbc

end AlgebraicGeometry.GroupoidsOver
