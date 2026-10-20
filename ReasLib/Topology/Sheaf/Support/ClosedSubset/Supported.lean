/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
public import ReasLib.Topology.Sheaf.Subset.General
public import ReasLib.Topology.Sheaf.Support.ClosedSubset.Kernel

/-!
# Restricting an ambient sheaf supported on a closed subset

An ambient support object can be recovered from its restriction to the closed subspace.
On an open of the subspace, the restriction is modeled by sections on its largest ambient
open. Extension to that open glues the original section with zero on the open complement.
The gluing maps come from the ambient sheaf condition, including for an empty cover.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite

noncomputable section

universe w u

namespace TopCat.Sheaf.ClosedSubset.SectionsWithSupport

variable {X : TopCat.{w}} {Z : Set X}
variable {C : Type u} [Category.{w} C]
variable {FC : C → C → Type w} {CC : C → Type w}
variable [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory.{w} C FC]
variable [IsAlgebraicStructure C (CategoryTheory.forget C)]
variable [HasColimits C] [HasZeroMorphisms C]

/-- A sheaf pushed forward from the closed subset restricts to zero on its open complement. -/
theorem restrictionPushforward_eq_zero (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf C) :
    restrictionToComplement hZ
      ((Sheaf.pushforward C (TopCat.subsetInclusion Z)).obj F) = 0 := sorry

/-- Factor a morphism vanishing on the open complement through the ambient support object. -/
def liftToObject (hZ : IsClosed Z) {G F : X.Sheaf C} (f : G ⟶ F)
    (hf : f ≫ restrictionToComplement hZ F = 0) : G ⟶ object hZ F :=
  kernel.lift _ f hf ≫
    (PreservesKernel.iso ((evaluation (X.Sheaf C) (X.Sheaf C)).obj F)
      (Sheaf.pullbackPushforwardAdjunction C (openComplementInclusion hZ)).unit).inv

/-- The support factorization recovers the original morphism after inclusion. -/
@[reassoc (attr := simp)]
theorem liftToObject_inclusion (hZ : IsClosed Z) {G F : X.Sheaf C} (f : G ⟶ F)
    (hf : f ≫ restrictionToComplement hZ F = 0) :
    liftToObject hZ f hf ≫ inclusion hZ F = f := sorry

/-- Sections of the ambient support object on the largest open with a prescribed trace.
Its gluing operation is inherited from the ambient sheaf, with a zero section added on the
open complement, so it also handles the empty covering family. -/
def supportedRestriction (hZ : IsClosed Z) (F : X.Sheaf C) :
    (TopCat.of Z).Sheaf C :=
  ⟨(TopCat.subsetInclusion_isInducing Z).functor.op ⋙ (object hZ F).obj,
    (Presheaf.isSheaf_iff_isSheafPairwiseIntersections _).mpr
      (fun ι U ↦ ⟨{
        lift := fun s ↦
          let V : Option ι → Opens X
            | none => openComplement hZ
            | some i => Subset.hull Z (U i)
          let c : Cone ((Pairwise.diagram V).op ⋙ (object hZ F).obj) :=
            { pt := s.pt
              π :=
                { app := by
                    rintro ⟨(_ | ⟨i, j⟩)⟩
                    · rename_i i
                      cases i with
                      | none => exact 0
                      | some i => exact s.π.app (op (.single i))
                    · cases i with
                      | none => exact 0
                      | some i =>
                        exact s.π.app (op (.single i)) ≫
                          (object hZ F).obj.map
                            (homOfLE (inf_le_left : V (some i) ⊓ V j ≤ _)).op
                  naturality := sorry } }
          ((Presheaf.isSheaf_iff_isSheafPairwiseIntersections (object hZ F).obj |>.mp
              (object hZ F).property) V).some.lift c ≫
            (object hZ F).obj.map
              (eqToHom (by sorry : Subset.hull Z (iSup U) = iSup V)).op
        fac := sorry
        uniq := sorry }⟩)⟩

/-- Extend a section of the ambient support object to the largest open with the same trace by
gluing it with zero on the complement. This construction is a morphism in the coefficient
category, rather than a choice of preimages of an asserted bijection. -/
def extendToHull (hZ : IsClosed Z) (F : X.Sheaf C) (V : Opens X) :
    (object hZ F).obj.obj (op V) ⟶
      (object hZ F).obj.obj
        (op (Subset.hull Z ((Opens.map (TopCat.subsetInclusion Z)).obj V))) :=
  ((object hZ F).isLimitPullbackCone V (openComplement hZ)).lift
      (PullbackCone.mk (𝟙 _) 0 (by sorry)) ≫
    (object hZ F).obj.map (homOfLE (by sorry :
      Subset.hull Z ((Opens.map (TopCat.subsetInclusion Z)).obj V) ≤
        V ⊔ openComplement hZ)).op

/-- Extending by zero and restricting back recovers the original section. -/
@[reassoc (attr := simp)]
theorem extendToHull_restrict (hZ : IsClosed Z) (F : X.Sheaf C) (V : Opens X) :
    extendToHull hZ F V ≫
      (object hZ F).obj.map (homOfLE (Subset.le_hull_map Z V)).op = 𝟙 _ := sorry

/-- The support object is the pushforward of its explicit restriction model. -/
def supportedRestrictionPushforwardIso (hZ : IsClosed Z) (F : X.Sheaf C) :
    object hZ F ≅
      (Sheaf.pushforward C (TopCat.subsetInclusion Z)).obj (supportedRestriction hZ F) where
  hom := ObjectProperty.homMk
    { app := fun V ↦ extendToHull hZ F V.unop
      naturality := sorry }
  inv := ObjectProperty.homMk
    { app := fun V ↦ (object hZ F).obj.map
        (homOfLE (Subset.le_hull_map Z V.unop)).op
      naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The inverse of the pullback-pushforward unit on an ambient support object, constructed
using extension by zero and the counit on its explicit restriction model. -/
def supportedUnitInv (hZ : IsClosed Z) (F : X.Sheaf C) :
    (Sheaf.pushforward C (TopCat.subsetInclusion Z)).obj
      ((Sheaf.pullback C (TopCat.subsetInclusion Z)).obj (object hZ F)) ⟶
        object hZ F :=
  (Sheaf.pushforward C (TopCat.subsetInclusion Z)).map
      ((Sheaf.pullback C (TopCat.subsetInclusion Z)).map
          (supportedRestrictionPushforwardIso hZ F).hom ≫
        (Sheaf.pullbackPushforwardAdjunction C (TopCat.subsetInclusion Z)).counit.app
          (supportedRestriction hZ F)) ≫
    (supportedRestrictionPushforwardIso hZ F).inv

/-- The support unit followed by its constructed inverse is the identity. -/
@[reassoc (attr := simp)]
theorem unit_supportedUnitInv (hZ : IsClosed Z) (F : X.Sheaf C) :
    (Sheaf.pullbackPushforwardAdjunction C (TopCat.subsetInclusion Z)).unit.app
        (object hZ F) ≫ supportedUnitInv hZ F = 𝟙 _ := sorry

/-- The constructed inverse followed by the support unit is the identity. -/
@[reassoc (attr := simp)]
theorem supportedUnitInv_unit (hZ : IsClosed Z) (F : X.Sheaf C) :
    supportedUnitInv hZ F ≫
      (Sheaf.pullbackPushforwardAdjunction C (TopCat.subsetInclusion Z)).unit.app
        (object hZ F) = 𝟙 _ := sorry

end TopCat.Sheaf.ClosedSubset.SectionsWithSupport

end
