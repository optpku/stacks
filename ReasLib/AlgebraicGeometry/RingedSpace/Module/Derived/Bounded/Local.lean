/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Restriction
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Locally bounded complexes and derived modules on ringed spaces

Local boundedness is owned by isomorphism-stable object properties.  The complex and derived
interfaces are symmetric in the upper and lower directions; representative theorems form the
bridge between them.
-/

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

namespace CochainComplex

/-- Complexes which become bounded above on a neighborhood of every point. -/
@[stacks 09V7 "locally bounded-above complexes"]
def locallyBoundedAbove :
    ObjectProperty (_root_.CochainComplex (Modules X) ℤ) :=
  fun K ↦ ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
    _root_.CochainComplex.minus
      (Modules (X.restrict U.isOpenEmbedding))
      ((moduleRestrictionComplexToOpen X U).obj K)

/-- A complex is locally bounded above when it belongs to `locallyBoundedAbove`. -/
@[stacks 09V7 "locally bounded-above complex predicate"]
abbrev IsLocallyBoundedAbove
    (K : _root_.CochainComplex (Modules X) ℤ) : Prop :=
  locallyBoundedAbove K

/-- Locally bounded-above complexes, as a full subcategory. -/
abbrev LocallyBoundedAbove :=
  (locallyBoundedAbove (X := X)).FullSubcategory

namespace LocallyBoundedAbove

/-- The canonical inclusion of locally bounded-above complexes. -/
abbrev ι : LocallyBoundedAbove (X := X) ⥤
    _root_.CochainComplex (Modules X) ℤ :=
  ObjectProperty.ι _

end LocallyBoundedAbove

/-- Complexes which become bounded below on a neighborhood of every point. -/
def locallyBoundedBelow :
    ObjectProperty (_root_.CochainComplex (Modules X) ℤ) :=
  fun K ↦ ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
    _root_.CochainComplex.plus
      (Modules (X.restrict U.isOpenEmbedding))
      ((moduleRestrictionComplexToOpen X U).obj K)

/-- A complex is locally bounded below when it belongs to `locallyBoundedBelow`. -/
abbrev IsLocallyBoundedBelow
    (K : _root_.CochainComplex (Modules X) ℤ) : Prop :=
  locallyBoundedBelow K

/-- Locally bounded-below complexes, as a full subcategory. -/
abbrev LocallyBoundedBelow :=
  (locallyBoundedBelow (X := X)).FullSubcategory

namespace LocallyBoundedBelow

/-- The canonical inclusion of locally bounded-below complexes. -/
abbrev ι : LocallyBoundedBelow (X := X) ⥤
    _root_.CochainComplex (Modules X) ℤ :=
  ObjectProperty.ι _

end LocallyBoundedBelow

/-- The neighborhoodwise characterization of local boundedness above. -/
theorem isLocallyBoundedAbove_iff
    (K : _root_.CochainComplex (Modules X) ℤ) :
    IsLocallyBoundedAbove K ↔
      ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
        _root_.CochainComplex.minus
          (Modules (X.restrict U.isOpenEmbedding))
          ((moduleRestrictionComplexToOpen X U).obj K) := Iff.rfl

/-- The neighborhoodwise characterization of local boundedness below. -/
theorem isLocallyBoundedBelow_iff
    (K : _root_.CochainComplex (Modules X) ℤ) :
    IsLocallyBoundedBelow K ↔
      ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
        _root_.CochainComplex.plus
          (Modules (X.restrict U.isOpenEmbedding))
          ((moduleRestrictionComplexToOpen X U).obj K) := Iff.rfl

/-- Local boundedness above is invariant under isomorphisms of complexes. -/
instance locallyBoundedAbove_isClosedUnderIsomorphisms :
    (locallyBoundedAbove (X := X)).IsClosedUnderIsomorphisms where
  of_iso := by
    intro K L e hK x
    obtain ⟨U, hx, hU⟩ := hK x
    exact ⟨U, hx, ObjectProperty.prop_of_iso _
      ((moduleRestrictionComplexToOpen X U).mapIso e) hU⟩

/-- Local boundedness below is invariant under isomorphisms of complexes. -/
instance locallyBoundedBelow_isClosedUnderIsomorphisms :
    (locallyBoundedBelow (X := X)).IsClosedUnderIsomorphisms where
  of_iso := by
    intro K L e hK x
    obtain ⟨U, hx, hU⟩ := hK x
    exact ⟨U, hx, ObjectProperty.prop_of_iso _
      ((moduleRestrictionComplexToOpen X U).mapIso e) hU⟩

/-- Transport local boundedness above along an isomorphism. -/
theorem IsLocallyBoundedAbove.of_iso
    {K L : _root_.CochainComplex (Modules X) ℤ}
    (hK : IsLocallyBoundedAbove K) (e : K ≅ L) :
    IsLocallyBoundedAbove L :=
  ObjectProperty.prop_of_iso locallyBoundedAbove e hK

/-- Transport local boundedness below along an isomorphism. -/
theorem IsLocallyBoundedBelow.of_iso
    {K L : _root_.CochainComplex (Modules X) ℤ}
    (hK : IsLocallyBoundedBelow K) (e : K ≅ L) :
    IsLocallyBoundedBelow L :=
  ObjectProperty.prop_of_iso locallyBoundedBelow e hK

/-- A globally bounded-above complex is locally bounded above. -/
theorem isLocallyBoundedAbove_of_minus
    {K : _root_.CochainComplex (Modules X) ℤ}
    (hK : _root_.CochainComplex.minus (Modules X) K) :
    IsLocallyBoundedAbove K := by
  obtain ⟨n, hn⟩ := hK
  intro x
  refine ⟨⊤, by trivial, n, ?_⟩
  infer_instance

/-- A globally bounded-below complex is locally bounded below. -/
theorem isLocallyBoundedBelow_of_plus
    {K : _root_.CochainComplex (Modules X) ℤ}
    (hK : _root_.CochainComplex.plus (Modules X) K) :
    IsLocallyBoundedBelow K := by
  obtain ⟨n, hn⟩ := hK
  intro x
  refine ⟨⊤, by trivial, n, ?_⟩
  infer_instance

end CochainComplex

namespace ModuleDerived

/-- Derived modules which are bounded above on a neighborhood of every point. -/
@[stacks 09V7 "locally bounded-above derived modules"]
def locallyBoundedAbove : ObjectProperty (ModuleDerived X) :=
  fun E ↦ ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
    ∃ n : ℤ, _root_.DerivedCategory.IsLE
      ((moduleRestrictionToOpenDerived X U).obj E) n

/-- A derived module is locally bounded above when it belongs to `locallyBoundedAbove`. -/
@[stacks 09V7 "locally bounded-above derived-module predicate"]
abbrev IsLocallyBoundedAbove (E : ModuleDerived X) : Prop :=
  locallyBoundedAbove E

/-- Locally bounded-above derived modules, as a full subcategory. -/
abbrev LocallyBoundedAbove :=
  (locallyBoundedAbove (X := X)).FullSubcategory

namespace LocallyBoundedAbove

/-- The canonical inclusion of locally bounded-above derived modules. -/
abbrev ι : LocallyBoundedAbove (X := X) ⥤ ModuleDerived X :=
  ObjectProperty.ι _

end LocallyBoundedAbove

/-- Derived modules which are bounded below on a neighborhood of every point. -/
@[stacks 0GM7 "locally bounded-below derived modules"]
def locallyBoundedBelow : ObjectProperty (ModuleDerived X) :=
  fun E ↦ ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
    ∃ n : ℤ, _root_.DerivedCategory.IsGE
      ((moduleRestrictionToOpenDerived X U).obj E) n

/-- A derived module is locally bounded below when it belongs to `locallyBoundedBelow`. -/
@[stacks 0GM7 "locally bounded-below derived-module predicate"]
abbrev IsLocallyBoundedBelow (E : ModuleDerived X) : Prop :=
  locallyBoundedBelow E

/-- Locally bounded-below derived modules, as a full subcategory. -/
abbrev LocallyBoundedBelow :=
  (locallyBoundedBelow (X := X)).FullSubcategory

namespace LocallyBoundedBelow

/-- The canonical inclusion of locally bounded-below derived modules. -/
abbrev ι : LocallyBoundedBelow (X := X) ⥤ ModuleDerived X :=
  ObjectProperty.ι _

end LocallyBoundedBelow

/-- The neighborhoodwise characterization of local boundedness above. -/
theorem isLocallyBoundedAbove_iff (E : ModuleDerived X) :
    E.IsLocallyBoundedAbove ↔
      ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
        ∃ n : ℤ, _root_.DerivedCategory.IsLE
          ((moduleRestrictionToOpenDerived X U).obj E) n := Iff.rfl

/-- The neighborhoodwise characterization of local boundedness below. -/
theorem isLocallyBoundedBelow_iff (E : ModuleDerived X) :
    E.IsLocallyBoundedBelow ↔
      ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
        ∃ n : ℤ, _root_.DerivedCategory.IsGE
          ((moduleRestrictionToOpenDerived X U).obj E) n := Iff.rfl

/-- A globally bounded-above derived module is locally bounded above. -/
theorem isLocallyBoundedAbove_of_isLE
    {E : ModuleDerived X} {n : ℤ}
    (hE : _root_.DerivedCategory.IsLE E n) :
    E.IsLocallyBoundedAbove := by
  letI := hE
  obtain ⟨K, hK, ⟨e⟩⟩ := _root_.DerivedCategory.exists_iso_Q_obj_of_isLE E n
  intro x
  refine ⟨⊤, by trivial, n, ?_⟩
  haveI : ((moduleRestrictionComplexToOpen X ⊤).obj K).IsStrictlyLE n :=
    inferInstance
  haveI : _root_.DerivedCategory.IsLE
      (DerivedCategory.Q.obj ((moduleRestrictionComplexToOpen X ⊤).obj K)) n :=
    (_root_.DerivedCategory.isLE_Q_obj_iff _ n).2 inferInstance
  exact _root_.DerivedCategory.TStructure.t.isLE_of_iso
    (((moduleRestrictionToOpenDerived X ⊤).mapIso e ≪≫
      moduleRestrictionToOpenDerivedFactors X ⊤ K).symm) n

/-- A globally bounded-below derived module is locally bounded below. -/
theorem isLocallyBoundedBelow_of_isGE
    {E : ModuleDerived X} {n : ℤ}
    (hE : _root_.DerivedCategory.IsGE E n) :
    E.IsLocallyBoundedBelow := by
  letI := hE
  obtain ⟨K, hK, ⟨e⟩⟩ := _root_.DerivedCategory.exists_iso_Q_obj_of_isGE E n
  intro x
  refine ⟨⊤, by trivial, n, ?_⟩
  haveI : ((moduleRestrictionComplexToOpen X ⊤).obj K).IsStrictlyGE n :=
    inferInstance
  haveI : _root_.DerivedCategory.IsGE
      (DerivedCategory.Q.obj ((moduleRestrictionComplexToOpen X ⊤).obj K)) n :=
    (_root_.DerivedCategory.isGE_Q_obj_iff _ n).2 inferInstance
  exact _root_.DerivedCategory.TStructure.t.isGE_of_iso
    (((moduleRestrictionToOpenDerived X ⊤).mapIso e ≪≫
      moduleRestrictionToOpenDerivedFactors X ⊤ K).symm) n

/-- Local boundedness above is invariant under isomorphisms of derived modules. -/
instance locallyBoundedAbove_isClosedUnderIsomorphisms :
    (locallyBoundedAbove (X := X)).IsClosedUnderIsomorphisms where
  of_iso := by
    intro E F e hE x
    obtain ⟨U, hx, n, hn⟩ := hE x
    letI := hn
    exact ⟨U, hx, n, _root_.DerivedCategory.TStructure.t.isLE_of_iso
      ((moduleRestrictionToOpenDerived X U).mapIso e) n⟩

/-- Local boundedness below is invariant under isomorphisms of derived modules. -/
instance locallyBoundedBelow_isClosedUnderIsomorphisms :
    (locallyBoundedBelow (X := X)).IsClosedUnderIsomorphisms where
  of_iso := by
    intro E F e hE x
    obtain ⟨U, hx, n, hn⟩ := hE x
    letI := hn
    exact ⟨U, hx, n, _root_.DerivedCategory.TStructure.t.isGE_of_iso
      ((moduleRestrictionToOpenDerived X U).mapIso e) n⟩

/-- Transport local boundedness above along an isomorphism. -/
theorem IsLocallyBoundedAbove.of_iso
    {E F : ModuleDerived X} (hE : E.IsLocallyBoundedAbove) (e : E ≅ F) :
    F.IsLocallyBoundedAbove :=
  ObjectProperty.prop_of_iso locallyBoundedAbove e hE

/-- Transport local boundedness below along an isomorphism. -/
theorem IsLocallyBoundedBelow.of_iso
    {E F : ModuleDerived X} (hE : E.IsLocallyBoundedBelow) (e : E ≅ F) :
    F.IsLocallyBoundedBelow :=
  ObjectProperty.prop_of_iso locallyBoundedBelow e hE

/-- Local boundedness above is equivalent to having a locally bounded-above representative. -/
theorem isLocallyBoundedAbove_iff_exists_representative (E : ModuleDerived X) :
    E.IsLocallyBoundedAbove ↔
      ∃ K : _root_.CochainComplex (Modules X) ℤ,
        ∃ _ : E ≅ DerivedCategory.Q.obj K,
          CochainComplex.IsLocallyBoundedAbove K := sorry

/-- Local boundedness below is equivalent to having a locally bounded-below representative. -/
theorem isLocallyBoundedBelow_iff_exists_representative (E : ModuleDerived X) :
    E.IsLocallyBoundedBelow ↔
      ∃ K : _root_.CochainComplex (Modules X) ℤ,
        ∃ _ : E ≅ DerivedCategory.Q.obj K,
          CochainComplex.IsLocallyBoundedBelow K := sorry

end ModuleDerived

namespace CochainComplex

/-- A locally bounded-above complex gives a locally bounded-above derived module. -/
theorem IsLocallyBoundedAbove.q_obj
    {K : _root_.CochainComplex (Modules X) ℤ}
    (hK : IsLocallyBoundedAbove K) :
    ModuleDerived.IsLocallyBoundedAbove (DerivedCategory.Q.obj K) := by
  intro x
  obtain ⟨U, hx, n, hn⟩ := hK x
  refine ⟨U, hx, n, ?_⟩
  haveI : _root_.DerivedCategory.IsLE
      (DerivedCategory.Q.obj ((moduleRestrictionComplexToOpen X U).obj K)) n :=
    (_root_.DerivedCategory.isLE_Q_obj_iff _ n).2 inferInstance
  exact _root_.DerivedCategory.TStructure.t.isLE_of_iso
    (moduleRestrictionToOpenDerivedFactors X U K).symm n

/-- A locally bounded-below complex gives a locally bounded-below derived module. -/
theorem IsLocallyBoundedBelow.q_obj
    {K : _root_.CochainComplex (Modules X) ℤ}
    (hK : IsLocallyBoundedBelow K) :
    ModuleDerived.IsLocallyBoundedBelow (DerivedCategory.Q.obj K) := by
  intro x
  obtain ⟨U, hx, n, hn⟩ := hK x
  refine ⟨U, hx, n, ?_⟩
  haveI : _root_.DerivedCategory.IsGE
      (DerivedCategory.Q.obj ((moduleRestrictionComplexToOpen X U).obj K)) n :=
    (_root_.DerivedCategory.isGE_Q_obj_iff _ n).2 inferInstance
  exact _root_.DerivedCategory.TStructure.t.isGE_of_iso
    (moduleRestrictionToOpenDerivedFactors X U K).symm n

end CochainComplex

end AlgebraicGeometry.RingedSpace
