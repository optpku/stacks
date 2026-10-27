/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback.RingModel

/-! # Composition isomorphisms for derived module pullback -/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Functor
open CategoryTheory.SimplicialSites

noncomputable section

universe u v w uC vC uD vD uH vH

namespace RingedSite.ToposHom.DerivedPullbackComposition

private def totalModel {C : Type uC} {D : Type uD} {H : Type uH}
    [Category.{vC} C] [Category.{vD} D] [Category.{vH} H]
    (F : C ⥤ H) (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [F.HasLeftDerivedFunctor W] : LeftDerived.Model F L W :=
  ⟨F.totalLeftDerived L W, F.totalLeftDerivedCounit L W, inferInstance⟩

variable {X Y Z : RingedSite.{u, v, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Z.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable (f : ToposHom X Y) (g : ToposHom Y Z) (h : ToposHom X Z)
variable [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} g.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} h.structureMap).IsRightAdjoint]
variable [HasModulePullbackDerived f] [HasModulePullbackDerived g]
variable [HasModulePullbackDerived h]
variable (hcomp : h.modulePullback ≅ g.modulePullback ⋙ f.modulePullback)

/-- The iterated homotopy-to-derived pullback functor. -/
abbrev iteratedToDerived : Hom.ModuleHomotopy.{w} Z ⥤ Hom.ModuleDerived.{w} X :=
  g.modulePullbackHomotopy ⋙ modulePullbackToDerived f

include hcomp in
/-- An underived composition identification transports existence of the total derived functor. -/
theorem hasLeftDerivedFunctor_iteratedToDerived :
    (iteratedToDerived f g).HasLeftDerivedFunctor (Hom.ModuleQis Z) :=
  (Functor.hasLeftDerivedFunctor_iff_of_iso
    (derivedPullbackCompToDerivedIso f g h hcomp) (Hom.ModuleQis Z)).mp inferInstance

private def iteratedModel : LeftDerived.Model (iteratedToDerived f g)
    (Hom.moduleLocalization Z) (Hom.ModuleQis Z) :=
  @totalModel _ _ _ _ _ _ (iteratedToDerived f g)
    (Hom.moduleLocalization Z) (Hom.ModuleQis Z) inferInstance
    (hasLeftDerivedFunctor_iteratedToDerived f g h hcomp)

/-- The total left derived functor of the iterated homotopy pullback. -/
abbrev iteratedDerived : Hom.ModuleDerived.{w} Z ⥤ Hom.ModuleDerived.{w} X :=
  (iteratedModel f g h hcomp).functor

/-- The total derived iterated model identifies with pullback along the composite. -/
def iteratedDerivedIso : iteratedDerived f g h hcomp ≅ h.modulePullbackDerived :=
  @Functor.leftDerivedNatIso _ _ _ _ _ _
    (iteratedDerived f g h hcomp) h.modulePullbackDerived
    (F := modulePullbackToDerived h) (F' := iteratedToDerived f g)
    (L := Hom.moduleLocalization Z)
    (iteratedModel f g h hcomp).counit
    ((modulePullbackToDerived h).totalLeftDerivedCounit
      (Hom.moduleLocalization Z) (Hom.ModuleQis Z))
    (Hom.ModuleQis Z) inferInstance inferInstance
    (iteratedModel f g h hcomp).isLeftDerived
    (derivedPullbackCompToDerivedIso f g h hcomp).symm

/-- The universal comparison from the composite pullback to the iterated total derived model. -/
def compositeToIterated :
    g.modulePullbackDerived ⋙ f.modulePullbackDerived ⟶ iteratedDerived f g h hcomp :=
  @Functor.leftDerivedLift _ _ _ _ _ _ (iteratedDerived f g h hcomp)
    (F := iteratedToDerived f g) (L := Hom.moduleLocalization Z)
    (iteratedModel f g h hcomp).counit (Hom.ModuleQis Z) inferInstance
    (iteratedModel f g h hcomp).isLeftDerived
    (g.modulePullbackDerived ⋙ f.modulePullbackDerived) (derivedPullbackCompCounit f g)

include hcomp in
/-- The fixed composite counit exhibits the composite pullback as left derived. -/
theorem isLeftDerivedFunctor_composite :
    (g.modulePullbackDerived ⋙ f.modulePullbackDerived).IsLeftDerivedFunctor
      (derivedPullbackCompCounit f g) (Hom.ModuleQis Z) where
  isRightKanExtension :=
    { nonempty_isUniversal :=
        ⟨DerivedPullbackCellModel.compositeTerminalWitness f g h hcomp⟩ }

/-- The reverse comparison is the explicit cell-augmentation universal extension map. -/
def iteratedToComposite :
    iteratedDerived f g h hcomp ⟶ g.modulePullbackDerived ⋙ f.modulePullbackDerived :=
  ((DerivedPullbackCellModel.compositeTerminalWitness f g h hcomp).lift
    (RightExtension.mk (iteratedDerived f g h hcomp)
      (iteratedModel f g h hcomp).counit))

/-- The forward universal lift followed by the reverse lift is the identity. -/
theorem compositeToIterated_comp_iteratedToComposite :
    compositeToIterated f g h hcomp ≫ iteratedToComposite f g h hcomp =
      𝟙 (g.modulePullbackDerived ⋙ f.modulePullbackDerived) := sorry

/-- The reverse universal lift followed by the forward lift is the identity. -/
theorem iteratedToComposite_comp_compositeToIterated :
    iteratedToComposite f g h hcomp ≫ compositeToIterated f g h hcomp =
      𝟙 (iteratedDerived f g h hcomp) := sorry

/-- The specified universal lifts identify composite pullback with the iterated derived model. -/
def compositeIsoIterated :
    g.modulePullbackDerived ⋙ f.modulePullbackDerived ≅ iteratedDerived f g h hcomp where
  hom := compositeToIterated f g h hcomp
  inv := iteratedToComposite f g h hcomp
  hom_inv_id := compositeToIterated_comp_iteratedToComposite f g h hcomp
  inv_hom_id := iteratedToComposite_comp_compositeToIterated f g h hcomp

/-- The canonical forward comparison followed by the constructed reverse comparison is identity. -/
theorem compComparison_hom_inv_id :
    derivedPullbackCompComparisonOf f g h hcomp ≫
        (compositeIsoIterated f g h hcomp ≪≫ iteratedDerivedIso f g h hcomp).inv =
      𝟙 (g.modulePullbackDerived ⋙ f.modulePullbackDerived) := sorry

/-- The constructed reverse comparison followed by the canonical forward comparison is identity. -/
theorem compComparison_inv_hom_id :
    (compositeIsoIterated f g h hcomp ≪≫ iteratedDerivedIso f g h hcomp).inv ≫
        derivedPullbackCompComparisonOf f g h hcomp = 𝟙 h.modulePullbackDerived := sorry

/-- The canonical derived comparison is an isomorphism, with inverse given by cell-model lifts. -/
def compComparisonIso :
    g.modulePullbackDerived ⋙ f.modulePullbackDerived ≅ h.modulePullbackDerived where
  hom := derivedPullbackCompComparisonOf f g h hcomp
  inv := (compositeIsoIterated f g h hcomp ≪≫ iteratedDerivedIso f g h hcomp).inv
  hom_inv_id := compComparison_hom_inv_id f g h hcomp
  inv_hom_id := compComparison_inv_hom_id f g h hcomp

/-- The forward map is the comparison determined by the original derived counits. -/
theorem compComparisonIso_hom :
    (compComparisonIso f g h hcomp).hom = derivedPullbackCompComparisonOf f g h hcomp := rfl

end RingedSite.ToposHom.DerivedPullbackComposition
