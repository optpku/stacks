/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction

@[expose] public section

noncomputable section

open CategoryTheory Limits
universe u

namespace CategoryTheory.Action.ModuleCat.DiscreteModuleCat

variable {R S G : Type u} [CommRing R] [CommRing S]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Restriction of scalars preserves the open-stabilizer condition. -/
theorem restrictScalars_mem (f : R →+* S) :
    openStabilizer S G ≤
      (openStabilizer R G).inverseImage ((ModuleCat.restrictScalars f).mapAction G) := sorry

/-- Restriction of scalars for discrete continuous module actions. -/
def restrictScalars (f : R →+* S) :
    DiscreteModuleCat S G ⥤ DiscreteModuleCat R G :=
  ObjectProperty.FullSubcategory.restrict
    ((ModuleCat.restrictScalars f).mapAction G) (restrictScalars_mem f)

/-- On objects, restriction of scalars is induced by the corresponding `ModuleCat` functor. -/
theorem restrictScalars_obj (f : R →+* S) (X : DiscreteModuleCat S G) :
    ((restrictScalars f).obj X).obj =
      ((ModuleCat.restrictScalars f).mapAction G).obj X.obj := sorry

/-- On morphisms, restriction of scalars is induced by the corresponding `ModuleCat` functor. -/
theorem restrictScalars_map (f : R →+* S) {X Y : DiscreteModuleCat S G}
    (g : X ⟶ Y) :
    ((restrictScalars f).map g).hom =
      ((ModuleCat.restrictScalars f).mapAction G).map g.hom := sorry

/-- Extension of scalars preserves the open-stabilizer condition. -/
theorem extendScalars_mem (f : R →+* S) :
    openStabilizer R G ≤
      (openStabilizer S G).inverseImage ((ModuleCat.extendScalars f).mapAction G) := sorry

/-- Extension of scalars for discrete continuous module actions. -/
def extendScalars (f : R →+* S) :
    DiscreteModuleCat R G ⥤ DiscreteModuleCat S G :=
  ObjectProperty.FullSubcategory.restrict
    ((ModuleCat.extendScalars f).mapAction G) (extendScalars_mem f)

/-- On objects, extension of scalars is induced by the corresponding `ModuleCat` functor. -/
theorem extendScalars_obj (f : R →+* S) (X : DiscreteModuleCat R G) :
    ((extendScalars f).obj X).obj =
      ((ModuleCat.extendScalars f).mapAction G).obj X.obj := sorry

/-- On morphisms, extension of scalars is induced by the corresponding `ModuleCat` functor. -/
theorem extendScalars_map (f : R →+* S) {X Y : DiscreteModuleCat R G}
    (g : X ⟶ Y) :
    ((extendScalars f).map g).hom =
      ((ModuleCat.extendScalars f).mapAction G).map g.hom := sorry

/-- The module morphism underlying the forward action-level adjunction equivalence. -/
def actionHomEquivToModule (f : R →+* S)
    {X : Action (ModuleCat R) G} {Y : Action (ModuleCat S) G}
    (g : ((ModuleCat.extendScalars f).mapAction G).obj X ⟶ Y) :
    X.V ⟶ (ModuleCat.restrictScalars f).obj Y.V :=
  (ModuleCat.extendRestrictScalarsAdj f).homEquiv X.V Y.V g.hom

/-- The forward module morphism commutes with the `G`-actions. -/
theorem actionHomEquivToModule_comm (f : R →+* S)
    {X : Action (ModuleCat R) G} {Y : Action (ModuleCat S) G}
    (g : ((ModuleCat.extendScalars f).mapAction G).obj X ⟶ Y) (a : G) :
    X.ρ a ≫ actionHomEquivToModule f g =
      actionHomEquivToModule f g ≫ (ModuleCat.restrictScalars f).map (Y.ρ a) := sorry

/-- The forward action morphism in the extension-restriction adjunction. -/
def actionHomEquivTo (f : R →+* S)
    {X : Action (ModuleCat R) G} {Y : Action (ModuleCat S) G}
    (g : ((ModuleCat.extendScalars f).mapAction G).obj X ⟶ Y) :
    X ⟶ ((ModuleCat.restrictScalars f).mapAction G).obj Y where
  hom := actionHomEquivToModule f g
  comm := actionHomEquivToModule_comm f g

/-- The module morphism underlying the inverse action-level adjunction equivalence. -/
def actionHomEquivInvModule (f : R →+* S)
    {X : Action (ModuleCat R) G} {Y : Action (ModuleCat S) G}
    (g : X ⟶ ((ModuleCat.restrictScalars f).mapAction G).obj Y) :
    (ModuleCat.extendScalars f).obj X.V ⟶ Y.V :=
  ((ModuleCat.extendRestrictScalarsAdj f).homEquiv X.V Y.V).symm g.hom

/-- The inverse module morphism commutes with the `G`-actions. -/
theorem actionHomEquivInvModule_comm (f : R →+* S)
    {X : Action (ModuleCat R) G} {Y : Action (ModuleCat S) G}
    (g : X ⟶ ((ModuleCat.restrictScalars f).mapAction G).obj Y) (a : G) :
    (ModuleCat.extendScalars f).map (X.ρ a) ≫ actionHomEquivInvModule f g =
      actionHomEquivInvModule f g ≫ Y.ρ a := sorry

/-- The inverse action morphism in the extension-restriction adjunction. -/
def actionHomEquivInv (f : R →+* S)
    {X : Action (ModuleCat R) G} {Y : Action (ModuleCat S) G}
    (g : X ⟶ ((ModuleCat.restrictScalars f).mapAction G).obj Y) :
    ((ModuleCat.extendScalars f).mapAction G).obj X ⟶ Y where
  hom := actionHomEquivInvModule f g
  comm := actionHomEquivInvModule_comm f g

/-- The inverse action-level adjunction map is a left inverse. -/
theorem actionHomEquiv_left_inv (f : R →+* S)
    {X : Action (ModuleCat R) G} {Y : Action (ModuleCat S) G}
    (g : ((ModuleCat.extendScalars f).mapAction G).obj X ⟶ Y) :
    actionHomEquivInv f (actionHomEquivTo f g) = g := sorry

/-- The inverse action-level adjunction map is a right inverse. -/
theorem actionHomEquiv_right_inv (f : R →+* S)
    {X : Action (ModuleCat R) G} {Y : Action (ModuleCat S) G}
    (g : X ⟶ ((ModuleCat.restrictScalars f).mapAction G).obj Y) :
    actionHomEquivTo f (actionHomEquivInv f g) = g := sorry

/-- The hom-set equivalence induced by extension and restriction of scalars on actions. -/
def actionHomEquiv (f : R →+* S)
    (X : Action (ModuleCat R) G) (Y : Action (ModuleCat S) G) :
    (((ModuleCat.extendScalars f).mapAction G).obj X ⟶ Y) ≃
      (X ⟶ ((ModuleCat.restrictScalars f).mapAction G).obj Y) where
  toFun := actionHomEquivTo f
  invFun := actionHomEquivInv f
  left_inv := actionHomEquiv_left_inv f
  right_inv := actionHomEquiv_right_inv f

/-- The action-level hom-set equivalence is natural in the source. -/
theorem actionHomEquiv_naturality_left_symm (f : R →+* S)
    {X' X : Action (ModuleCat R) G} {Y : Action (ModuleCat S) G}
    (g : X' ⟶ X) (h : X ⟶ ((ModuleCat.restrictScalars f).mapAction G).obj Y) :
    (actionHomEquiv f X' Y).symm (g ≫ h) =
      ((ModuleCat.extendScalars f).mapAction G).map g ≫
        (actionHomEquiv f X Y).symm h := sorry

/-- The action-level hom-set equivalence is natural in the target. -/
theorem actionHomEquiv_naturality_right (f : R →+* S)
    {X : Action (ModuleCat R) G} {Y Y' : Action (ModuleCat S) G}
    (g : ((ModuleCat.extendScalars f).mapAction G).obj X ⟶ Y) (h : Y ⟶ Y') :
    actionHomEquiv f X Y' (g ≫ h) =
      actionHomEquiv f X Y g ≫
        ((ModuleCat.restrictScalars f).mapAction G).map h := sorry

/-- Extension and restriction of scalars are adjoint on categories of module actions. -/
def actionExtendRestrictAdjunction (f : R →+* S) :
    (ModuleCat.extendScalars f).mapAction G ⊣
      (ModuleCat.restrictScalars f).mapAction G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := actionHomEquiv f
      homEquiv_naturality_left_symm := actionHomEquiv_naturality_left_symm f
      homEquiv_naturality_right := actionHomEquiv_naturality_right f }

/-- Extension and restriction of scalars are adjoint on discrete continuous module actions. -/
def extendRestrictAdjunction (f : R →+* S) :
    (extendScalars f : DiscreteModuleCat R G ⥤ DiscreteModuleCat S G) ⊣
      (restrictScalars f : DiscreteModuleCat S G ⥤ DiscreteModuleCat R G) :=
  ObjectProperty.FullSubcategory.adjunction
    ((ModuleCat.extendScalars f).mapAction G)
    ((ModuleCat.restrictScalars f).mapAction G)
    (actionExtendRestrictAdjunction f) (extendScalars_mem f) (restrictScalars_mem f)

/-- The unit of the discrete extension-restriction adjunction is the underlying module unit. -/
theorem extendRestrictAdjunction_unit_app (f : R →+* S)
    (X : DiscreteModuleCat R G) :
    ((extendRestrictAdjunction f).unit.app X).hom.hom =
      (ModuleCat.extendRestrictScalarsAdj f).unit.app X.obj.V := sorry

/-- The counit of the discrete extension-restriction adjunction is the underlying module counit. -/
theorem extendRestrictAdjunction_counit_app (f : R →+* S)
    (Y : DiscreteModuleCat S G) :
    ((extendRestrictAdjunction f).counit.app Y).hom.hom =
      (ModuleCat.extendRestrictScalarsAdj f).counit.app Y.obj.V := sorry

/-- Restriction of scalars on discrete continuous modules preserves finite colimits. -/
instance restrictScalarsPreservesFiniteColimits (f : R →+* S) :
    PreservesFiniteColimits
      (restrictScalars f : DiscreteModuleCat S G ⥤ DiscreteModuleCat R G) := sorry

/-- The trivial regular action has open stabilizers. -/
theorem trivialCoefficient_mem (R G : Type u) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    openStabilizer R G (Action.trivial G (ModuleCat.of R R)) := sorry

/-- The regular coefficient module with the trivial `G`-action. -/
def trivialCoefficient (R G : Type u) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] : DiscreteModuleCat R G :=
  ⟨Action.trivial G (ModuleCat.of R R), trivialCoefficient_mem R G⟩

/-- The underlying action of `trivialCoefficient` is the trivial regular action. -/
theorem trivialCoefficient_obj (R G : Type u) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    (trivialCoefficient R G).obj = Action.trivial G (ModuleCat.of R R) := sorry

/-- The integral scalar map into the restricted regular `R`-module. -/
def intCastModuleHom (R : Type) [CommRing R] :
    ModuleCat.of ℤ ℤ ⟶
      (ModuleCat.restrictScalars (Int.castRingHom R)).obj (ModuleCat.of R R) :=
  ModuleCat.semilinearMapAddEquiv (Int.castRingHom R)
    (ModuleCat.of ℤ ℤ) (ModuleCat.of R R) (Int.castRingHom R).toSemilinearMap

/-- The canonical module map `R ⊗[ℤ] ℤ ⟶ R`. -/
def extendTrivialModuleHom (R : Type) [CommRing R] :
    (ModuleCat.extendScalars (Int.castRingHom R)).obj (ModuleCat.of ℤ ℤ) ⟶
      ModuleCat.of R R :=
  ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom R)).homEquiv
    (ModuleCat.of ℤ ℤ) (ModuleCat.of R R)).symm (intCastModuleHom R)

/-- The canonical map `R ⊗[ℤ] ℤ ⟶ R` is equivariant for the trivial actions. -/
theorem extendTrivialModuleHom_comm (R G : Type) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (a : G) :
    (((ModuleCat.extendScalars (Int.castRingHom R)).mapAction G).obj
        (Action.trivial G (ModuleCat.of ℤ ℤ))).ρ a ≫ extendTrivialModuleHom R =
      extendTrivialModuleHom R ≫ (Action.trivial G (ModuleCat.of R R)).ρ a := sorry

/-- The canonical equivariant map from the extended integral trivial coefficient to the
`R`-linear trivial coefficient. -/
def extendTrivialActionHom (R G : Type) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    ((ModuleCat.extendScalars (Int.castRingHom R)).mapAction G).obj
        (Action.trivial G (ModuleCat.of ℤ ℤ)) ⟶
      Action.trivial G (ModuleCat.of R R) where
  hom := extendTrivialModuleHom R
  comm := extendTrivialModuleHom_comm R G

/-- The canonical comparison from the scalar extension of the integral trivial coefficient to
the `R`-linear trivial coefficient. -/
def extendTrivialHom (R G : Type) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    (extendScalars (Int.castRingHom R)).obj (trivialCoefficient ℤ G) ⟶
      trivialCoefficient R G :=
  ObjectProperty.homMk (extendTrivialActionHom R G)

/-- The comparison on trivial coefficients is induced by the tensor-product right unitor. -/
theorem extendTrivialHom_apply (R G : Type) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (x : ((extendScalars (Int.castRingHom R)).obj (trivialCoefficient ℤ G)).obj.V) :
    (extendTrivialHom R G).hom.hom x =
      ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom R)).homEquiv
        (ModuleCat.of ℤ ℤ) (ModuleCat.of R R)).symm (intCastModuleHom R) x := sorry

/-- The canonical comparison on trivial coefficients is an isomorphism. -/
instance instIsIsoExtendTrivialHom (R G : Type) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] : IsIso (extendTrivialHom R G) := sorry

end CategoryTheory.Action.ModuleCat.DiscreteModuleCat
