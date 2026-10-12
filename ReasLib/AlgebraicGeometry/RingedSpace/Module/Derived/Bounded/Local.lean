/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
          ((moduleRestrictionComplexToOpen X U).obj K) := sorry

/-- The neighborhoodwise characterization of local boundedness below. -/
theorem isLocallyBoundedBelow_iff
    (K : _root_.CochainComplex (Modules X) ℤ) :
    IsLocallyBoundedBelow K ↔
      ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
        _root_.CochainComplex.plus
          (Modules (X.restrict U.isOpenEmbedding))
          ((moduleRestrictionComplexToOpen X U).obj K) := sorry

/-- Local boundedness above is invariant under isomorphisms of complexes. -/
instance locallyBoundedAbove_isClosedUnderIsomorphisms :
    (locallyBoundedAbove (X := X)).IsClosedUnderIsomorphisms := sorry

/-- Local boundedness below is invariant under isomorphisms of complexes. -/
instance locallyBoundedBelow_isClosedUnderIsomorphisms :
    (locallyBoundedBelow (X := X)).IsClosedUnderIsomorphisms := sorry

/-- Transport local boundedness above along an isomorphism. -/
theorem IsLocallyBoundedAbove.of_iso
    {K L : _root_.CochainComplex (Modules X) ℤ}
    (hK : IsLocallyBoundedAbove K) (e : K ≅ L) :
    IsLocallyBoundedAbove L := sorry

/-- Transport local boundedness below along an isomorphism. -/
theorem IsLocallyBoundedBelow.of_iso
    {K L : _root_.CochainComplex (Modules X) ℤ}
    (hK : IsLocallyBoundedBelow K) (e : K ≅ L) :
    IsLocallyBoundedBelow L := sorry

/-- A globally bounded-above complex is locally bounded above. -/
theorem isLocallyBoundedAbove_of_minus
    {K : _root_.CochainComplex (Modules X) ℤ}
    (hK : _root_.CochainComplex.minus (Modules X) K) :
    IsLocallyBoundedAbove K := sorry

/-- A globally bounded-below complex is locally bounded below. -/
theorem isLocallyBoundedBelow_of_plus
    {K : _root_.CochainComplex (Modules X) ℤ}
    (hK : _root_.CochainComplex.plus (Modules X) K) :
    IsLocallyBoundedBelow K := sorry

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
          ((moduleRestrictionToOpenDerived X U).obj E) n := sorry

/-- The neighborhoodwise characterization of local boundedness below. -/
theorem isLocallyBoundedBelow_iff (E : ModuleDerived X) :
    E.IsLocallyBoundedBelow ↔
      ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
        ∃ n : ℤ, _root_.DerivedCategory.IsGE
          ((moduleRestrictionToOpenDerived X U).obj E) n := sorry

/-- A globally bounded-above derived module is locally bounded above. -/
theorem isLocallyBoundedAbove_of_isLE
    {E : ModuleDerived X} {n : ℤ}
    (hE : _root_.DerivedCategory.IsLE E n) :
    E.IsLocallyBoundedAbove := sorry

/-- A globally bounded-below derived module is locally bounded below. -/
theorem isLocallyBoundedBelow_of_isGE
    {E : ModuleDerived X} {n : ℤ}
    (hE : _root_.DerivedCategory.IsGE E n) :
    E.IsLocallyBoundedBelow := sorry

/-- Local boundedness above is invariant under isomorphisms of derived modules. -/
instance locallyBoundedAbove_isClosedUnderIsomorphisms :
    (locallyBoundedAbove (X := X)).IsClosedUnderIsomorphisms := sorry

/-- Local boundedness below is invariant under isomorphisms of derived modules. -/
instance locallyBoundedBelow_isClosedUnderIsomorphisms :
    (locallyBoundedBelow (X := X)).IsClosedUnderIsomorphisms := sorry

/-- Transport local boundedness above along an isomorphism. -/
theorem IsLocallyBoundedAbove.of_iso
    {E F : ModuleDerived X} (hE : E.IsLocallyBoundedAbove) (e : E ≅ F) :
    F.IsLocallyBoundedAbove := sorry

/-- Transport local boundedness below along an isomorphism. -/
theorem IsLocallyBoundedBelow.of_iso
    {E F : ModuleDerived X} (hE : E.IsLocallyBoundedBelow) (e : E ≅ F) :
    F.IsLocallyBoundedBelow := sorry

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
    ModuleDerived.IsLocallyBoundedAbove (DerivedCategory.Q.obj K) := sorry

/-- A locally bounded-below complex gives a locally bounded-below derived module. -/
theorem IsLocallyBoundedBelow.q_obj
    {K : _root_.CochainComplex (Modules X) ℤ}
    (hK : IsLocallyBoundedBelow K) :
    ModuleDerived.IsLocallyBoundedBelow (DerivedCategory.Q.obj K) := sorry

end CochainComplex

end AlgebraicGeometry.RingedSpace
