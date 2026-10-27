/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Pullback.Coherence
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.SpaceComparison

/-! # Composition and two-cell coherence for quasi-coherent pullback -/

@[expose] public section
set_option backward.privateInPublic true
open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.GroupoidsOver
open CategoryTheory.ObjectProperty
open FiberedCategoryOver.Groupoids
open scoped Bicategory
noncomputable section
universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh
variable {S : Scheme.{u}}

/-- The component comparison for quasi-coherent two-isomorphism transport. -/
private def pullbackIso_component {X Y : GroupoidsOver S} {f g : X ⟶ Y} (e : f ≅ g) (F : QCoh Y) :
    (pullback g).obj F ≅ (pullback f).obj F :=
  (fun F =>
      (quasiCoherentModuleProperty X).isoMk
        ((FullSubcategory.restrict.compιIso (modulePullback g)
            (modulePullback_le_inverseImage g)).app F ≪≫
          ((modulePullbackIso e).app F.obj).symm ≪≫
            (FullSubcategory.restrict.compιIso (modulePullback f)
                (modulePullback_le_inverseImage f)).symm.app F)) F

/-- The component comparisons commute with morphisms of quasi-coherent modules. -/
private theorem pullbackIso_laws {X Y : GroupoidsOver S} {f g : X ⟶ Y} (e : f ≅ g)
    {M N : QCoh Y} (a : M ⟶ N) :
    (pullback g).map a ≫ (pullbackIso_component e N).hom =
      (pullbackIso_component e M).hom ≫ (pullback f).map a := sorry

/-- Restriction of a 2-isomorphism of 1-morphisms to quasi-coherent pullbacks. -/
def pullbackIso {X Y : GroupoidsOver S} {f g : X ⟶ Y} (e : f ≅ g) :
    pullback g ≅ pullback f :=
  NatIso.ofComponents (pullbackIso_component e) (fun a => pullbackIso_laws e a)

/-- The component comparison for quasi-coherent composite pullback. -/
private def pullback_comp_component {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) (F : QCoh Z) :
    (pullback (f ≫ g)).obj F ≅ (pullback g ⋙ pullback f).obj F :=
  (fun F =>
      (quasiCoherentModuleProperty X).isoMk
        ((FullSubcategory.restrict.compιIso (modulePullback (f ≫ g))
            (modulePullback_le_inverseImage (f ≫ g))).app F ≪≫
          ((modulePullback_comp f g).app F.obj).symm ≪≫
            (modulePullback f).mapIso
              ((FullSubcategory.restrict.compιIso (modulePullback g)
                  (modulePullback_le_inverseImage g)).symm.app F) ≪≫
              (FullSubcategory.restrict.compιIso (modulePullback f)
                  (modulePullback_le_inverseImage f)).symm.app
                ((pullback g).obj F))) F

/-- The component comparisons commute with morphisms of quasi-coherent modules. -/
private theorem pullback_comp_laws {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M N : QCoh Z} (a : M ⟶ N) :
    (pullback (f ≫ g)).map a ≫ (pullback_comp_component f g N).hom =
      (pullback_comp_component f g M).hom ≫ (pullback g ⋙ pullback f).map a := sorry

/-- Composition of quasi-coherent pullbacks along a composite 1-morphism. -/
def pullback_comp {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  NatIso.ofComponents (pullback_comp_component f g) (fun a => pullback_comp_laws f g a)

/-- The component of contravariant pullback transport along a two-cell. -/
private def pullbackMap_component {X Y : GroupoidsOver S} {f g : X ⟶ Y} (α : f ⟶ g) (F : QCoh Y) :
    (pullback g).obj F ⟶ (pullback f).obj F :=
    (quasiCoherentModuleProperty X).homMk
      ((FullSubcategory.restrict.compιIso (modulePullback g)
          (modulePullback_le_inverseImage g)).hom.app F ≫
        (modulePullbackHom α).app F.obj ≫
          (FullSubcategory.restrict.compιIso (modulePullback f)
              (modulePullback_le_inverseImage f)).inv.app F)

/-- Two-cell pullback components commute with morphisms of quasi-coherent modules. -/
private theorem pullbackMap_laws {X Y : GroupoidsOver S} {f g : X ⟶ Y} (α : f ⟶ g)
    {M N : QCoh Y} (a : M ⟶ N) :
    (pullback g).map a ≫ pullbackMap_component α N =
      pullbackMap_component α M ≫ (pullback f).map a := sorry

/-- Restriction of a `2`-cell of 1-morphisms to quasi-coherent pullbacks. -/
def pullbackMap {X Y : GroupoidsOver S} {f g : X ⟶ Y} (α : f ⟶ g) :
    pullback g ⟶ pullback f where
  app := pullbackMap_component α
  naturality _ _ a := pullbackMap_laws α a

/-- Underlying sheaf of `QCoh.pullback f` compared with `modulePullback f`. -/
def pullback_compιIso {X Y : GroupoidsOver S} (f : X ⟶ Y) (F : QCoh Y) :
    ((pullback f).obj F).obj ≅ (modulePullback f).obj F.obj :=
  (FullSubcategory.restrict.compιIso (modulePullback f)
      (modulePullback_le_inverseImage f)).app F

/-- The algebraic-space morphism recovered from a represented morphism with
identity presentations is the original morphism. -/
theorem moduleComparisonSpaceMorphism_toGroupoids {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    moduleComparisonSpaceMorphism (AlgebraicSpace.toGroupoids.map f)
      (Bicategory.Equivalence.id X.toGroupoids) (Bicategory.Equivalence.id Y.toGroupoids) = f :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
