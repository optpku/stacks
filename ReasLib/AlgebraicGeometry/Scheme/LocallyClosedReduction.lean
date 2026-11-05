/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.Topology.LocallyClosed.Subsets

/-!
# Reduced induced schemes on locally closed subsets

The open ambient subscheme, closed subset, vanishing ideal, resulting scheme,
and immersion are all explicit reusable data.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.LocallyClosedReduction

variable {X : Scheme.{u}}

/-- The open complement of the boundary of a bundled locally closed subset. -/
@[stacks 0F2L "ambient open of a locally closed reduction"]
def ambientOpen (T : LocallyCloseds X) : X.Opens :=
  ⟨coborder T, T.property.isOpen_coborder⟩

/-- The underlying set of the ambient open is the coborder of `T`. -/
@[simp, stacks 0F2L "ambient open underlying set"]
theorem coe_ambientOpen (T : LocallyCloseds X) :
    (ambientOpen T : Set X) = coborder T := rfl

/-- The locally closed subset, viewed as a closed subset of its ambient open subscheme. -/
@[stacks 0F2L "closed subset in the ambient open"]
def closedSubset (T : LocallyCloseds X) :
    Closeds (ambientOpen T).toScheme :=
  ⟨(ambientOpen T).ι ⁻¹' T, isClosed_preimage_val_coborder⟩

/-- The closed subset is the inverse image of `T` under the open-subscheme inclusion. -/
@[stacks 0F2L "locally closed subset in the ambient open"]
theorem coe_closedSubset (T : LocallyCloseds X) :
    (closedSubset T : Set (ambientOpen T).toScheme) =
      (ambientOpen T).ι ⁻¹' T := rfl

/-- The reduced closed-subscheme structure on the locally closed subset inside its ambient
open. -/
@[stacks 0F2L "closed stage of a locally closed reduction"]
noncomputable abbrev closedStructure (T : LocallyCloseds X) :
    ClosedSubschemeStructure (closedSubset T) :=
  ClosedSubschemeStructure.reduced (closedSubset T)

/-- The vanishing ideal defining the reduced induced scheme on a locally closed subset. -/
@[stacks 0F2L "ideal of a locally closed reduction"]
abbrev ideal (T : LocallyCloseds X) :
    (ambientOpen T).toScheme.IdealSheafData :=
  (closedStructure T).ideal

/-- The defining ideal has the prescribed closed support in the ambient open. -/
@[stacks 0F2L "locally closed reduction ideal support"]
theorem support_ideal (T : LocallyCloseds X) :
    (ideal T).support = closedSubset T :=
  IdealSheafData.support_vanishingIdeal _

/-- The reduced induced scheme on a locally closed subset. -/
@[stacks 0F2L "scheme on a locally closed subset"]
abbrev scheme (T : LocallyCloseds X) : Scheme.{u} :=
  (closedStructure T).subscheme

/-- The closed immersion into the ambient open subscheme. -/
@[stacks 0F2L "closed stage of a locally closed reduction"]
abbrev ιToAmbientOpen (T : LocallyCloseds X) :
    scheme T ⟶ (ambientOpen T).toScheme :=
  (closedStructure T).ι

/-- The closed stage has image equal to the prescribed closed subset. -/
@[stacks 0F2L, simp]
theorem range_ιToAmbientOpen (T : LocallyCloseds X) :
    Set.range (ιToAmbientOpen T) = closedSubset T :=
  IdealSheafData.range_vanishingIdeal_subschemeι _

/-- The canonical immersion of the locally closed reduced induced scheme into `X`. -/
@[stacks 0F2L "locally closed reduction immersion"]
abbrev ι (T : LocallyCloseds X) : scheme T ⟶ X :=
  ιToAmbientOpen T ≫ (ambientOpen T).ι

/-- The locally closed induced scheme is reduced. -/
@[stacks 0F2L "locally closed reduction is reduced", instance]
instance scheme_isReduced (T : LocallyCloseds X) :
    IsReduced (scheme T) := by
  change IsReduced (IdealSheafData.vanishingIdeal (closedSubset T)).subscheme
  infer_instance

/-- The canonical map of a locally closed induced scheme is an immersion. -/
@[stacks 0F2L "locally closed reduction immersion instance", instance]
instance ι_isImmersion (T : LocallyCloseds X) :
    IsImmersion (ι T) :=
  inferInstance

/-- The canonical immersion has set-theoretic range exactly `T`. -/
@[stacks 0F2L, simp]
theorem range_ι (T : LocallyCloseds X) :
    Set.range (ι T) = T := by
  change Set.range ((ambientOpen T).ι ∘ ιToAmbientOpen T) = T
  rw [Set.range_comp, range_ιToAmbientOpen, coe_closedSubset,
    Set.image_preimage_eq_inter_range, Opens.range_ι]
  exact Set.inter_eq_left.mpr subset_coborder

/-- A map into a locally closed subset factors explicitly through its ambient
open. The range hypothesis is only used in the open-immersion lift. -/
noncomputable def liftToAmbientOpen (T : LocallyCloseds X) {Y : Scheme.{u}}
    (g : Y ⟶ X) (h : Set.range g ⊆ T) : Y ⟶ (ambientOpen T).toScheme :=
  IsOpenImmersion.lift (ambientOpen T).ι g (by
    rw [Opens.range_ι, coe_ambientOpen]
    exact h.trans subset_coborder)

@[reassoc (attr := simp)]
theorem liftToAmbientOpen_ι (T : LocallyCloseds X) {Y : Scheme.{u}}
    (g : Y ⟶ X) (h : Set.range g ⊆ T) :
    liftToAmbientOpen T g h ≫ (ambientOpen T).ι = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- A morphism from a reduced scheme whose image lies in a closed subset
annihilates its vanishing ideal. This uses the actual kernel ideal of the map. -/
theorem vanishingIdeal_le_ker_of_range_subset {Y Z : Scheme.{u}} [IsReduced Y]
    (g : Y ⟶ Z) (T : Closeds Z) (h : Set.range g ⊆ T) :
    IdealSheafData.vanishingIdeal T ≤ g.ker := by
  have hbot : (IdealSheafData.vanishingIdeal (⊤ : Closeds Y)) = ⊥ := by
    rw [IdealSheafData.vanishingIdeal_top, nilradical_eq_bot]
  rw [← IdealSheafData.map_bot g, ← hbot, IdealSheafData.map_vanishingIdeal]
  apply IdealSheafData.vanishingIdeal_antimono
  change closure (g '' (Set.univ : Set Y)) ⊆ T
  rw [Set.image_univ]
  exact T.isClosed.closure_subset_iff.mpr h

/-- A morphism from a reduced scheme into `T` lifts through its reduced induced
scheme structure. The map is the explicit open lift followed by mathlib's
closed-immersion lift, whose kernel-containment certificate is proved above. -/
noncomputable def lift (T : LocallyCloseds X) {Y : Scheme.{u}} [IsReduced Y]
    (g : Y ⟶ X) (h : Set.range g ⊆ T) : Y ⟶ scheme T :=
  IsClosedImmersion.lift (ιToAmbientOpen T) (liftToAmbientOpen T g h) (by
    change (ideal T).subschemeι.ker ≤ (liftToAmbientOpen T g h).ker
    rw [IdealSheafData.ker_subschemeι]
    apply vanishingIdeal_le_ker_of_range_subset
    rintro _ ⟨y, rfl⟩
    change (ambientOpen T).ι (liftToAmbientOpen T g h y) ∈ (T : Set X)
    rw [← Scheme.Hom.comp_apply, liftToAmbientOpen_ι]
    exact h ⟨y, rfl⟩)

@[reassoc (attr := simp)]
theorem lift_ι (T : LocallyCloseds X) {Y : Scheme.{u}} [IsReduced Y]
    (g : Y ⟶ X) (h : Set.range g ⊆ T) :
    lift T g h ≫ ι T = g := by
  rw [ι, ← Category.assoc, lift, IsClosedImmersion.lift_fac,
    liftToAmbientOpen_ι]

end AlgebraicGeometry.Scheme.LocallyClosedReduction
