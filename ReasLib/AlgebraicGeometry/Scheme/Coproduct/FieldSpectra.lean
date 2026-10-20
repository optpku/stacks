/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Comma.Over.Mono
public import ReasLib.AlgebraicGeometry.Scheme.Coproduct.Subfamily
public import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Monomorphisms into coproducts of spectra of fields
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.Coproduct.FieldSpectra

/-- The coproduct of spectra associated to a family of fields. -/
@[stacks 03DP "coproduct field-spectrum family"]
noncomputable abbrev family {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)] : Scheme.{v} :=
  ∐ fun i ↦ Spec (CommRingCat.of (k i))

/-- The coproduct of field spectra over the indices in `J`. -/
@[stacks 03DP "coproduct field-spectrum subfamily"]
noncomputable abbrev subfamily {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)] (J : Set ι) : Scheme.{v} :=
  Coproduct.subfamily (fun i ↦ Spec (CommRingCat.of (k i))) J

/-- The canonical inclusion of a subfamily of field spectra. -/
@[stacks 03DP "coproduct field-spectrum inclusion"]
noncomputable abbrev inclusion {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)] (J : Set ι) :
    subfamily k J ⟶ family k :=
  Coproduct.inclusion (fun i ↦ Spec (CommRingCat.of (k i))) J

/-- The field-spectrum summands met by a morphism into their coproduct. -/
@[stacks 03DP "support in a coproduct of field spectra"]
def support {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)]
    {Y : Scheme.{v}} (f : Y ⟶ family k) : Set ι :=
  Coproduct.support (fun i ↦ Spec (CommRingCat.of (k i))) f

/-- Membership in field-spectrum support means that the image meets the corresponding
coproduct summand. -/
@[stacks 03DP "coproduct field-spectrum support membership"]
theorem mem_support_iff {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)]
    {Y : Scheme.{v}} (f : Y ⟶ family k) (i : ι) :
    i ∈ support k f ↔
      ∃ y : Y, f.base y ∈
        (Sigma.ι (fun j ↦ Spec (CommRingCat.of (k j))) i).opensRange := sorry

/-- The support of a subfamily inclusion is exactly its indexing subset. -/
@[simp, stacks 03DP "coproduct field-spectrum inclusion support"]
theorem support_inclusion {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)] (J : Set ι) :
    support k (inclusion k J) = J := sorry

/-- Support is unchanged under an isomorphic change of source over the ambient coproduct. -/
@[stacks 03DP "coproduct field-spectrum support invariance"]
theorem support_congr {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)]
    {X Y : Scheme.{v}}
    (f : X ⟶ family k) (g : Y ⟶ family k)
    (e : X ≅ Y) (h : e.hom ≫ g = f) :
    support k f = support k g := sorry

/-- The subobject represented by the inclusion of the summands indexed by `J`. -/
@[stacks 03DP "field-spectrum coproduct subobject on a subset"]
noncomputable def subsetSubobject {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)] (J : Set ι) :
    Subobject (family k) :=
  Subobject.mk (inclusion k J)

/-- The support of a coproduct subobject, independent of a chosen monomorphism representing it. -/
@[stacks 03DP "support of a field-spectrum coproduct subobject"]
def subobjectSupport {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)] :
    Subobject (family k) → Set ι :=
  Subobject.lift (fun _ f _ => support k f)
    (fun {A B} (f : A ⟶ family k) (g : B ⟶ family k)
      [h_f : Mono f] [h_g : Mono g] (i : A ≅ B) (h : i.hom ≫ g = f) =>
      support_congr k f g i h)

/-- Computing subobject support on a representative recovers the support of that
representative. -/
@[simp, stacks 03DP]
theorem subobjectSupport_mk {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)]
    {X : Scheme.{v}} (f : X ⟶ family k) [Mono f] :
    subobjectSupport k (Subobject.mk f) = support k f := sorry

/-- The support of the subobject attached to `J` is exactly `J`. -/
@[simp, stacks 03DP]
theorem subobjectSupport_subsetSubobject {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)] (J : Set ι) :
    subobjectSupport k (subsetSubobject k J) = J := sorry

/-- A monomorphism into a coproduct of field spectra is canonically classified by the
summands met by its image. -/
@[stacks 03DP]
theorem support_isoOver_of_mono {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)]
    {Y : Scheme.{v}} (f : Y ⟶ family k) [Mono f] :
    Nonempty (Over.mk f ≅ Over.mk (inclusion k (support k f))) := sorry

/-- A monomorphism is explicitly isomorphic to its support subfamily, with the isomorphism
commuting with the maps to the ambient coproduct. -/
@[stacks 03DP "explicit support classification"]
theorem exists_iso_support {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)]
    {Y : Scheme.{v}} (f : Y ⟶ family k) [Mono f] :
    ∃ e : Y ≅ subfamily k (support k f),
      e.hom ≫ inclusion k (support k f) = f := sorry

/-- Any subcoproduct model of a monomorphism uses exactly its support. -/
@[stacks 03DP]
theorem support_eq_of_isoOver {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)]
    {Y : Scheme.{v}} (f : Y ⟶ family k) (J : Set ι)
    (h : Nonempty (Over.mk f ≅ Over.mk (inclusion k J))) :
    support k f = J := sorry

/-- A monomorphism into a coproduct of field spectra represents exactly the subobject indexed by
its support. -/
@[stacks 03DP "field-spectrum coproduct subobject classified by support"]
theorem subobject_eq_support {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)]
    {Y : Scheme.{v}} (f : Y ⟶ family k) [Mono f] :
    Subobject.mk f = subsetSubobject k (support k f) := sorry

/-- Reconstructing a coproduct subobject from its support gives the original subobject. -/
@[simp, stacks 03DP]
theorem subsetSubobject_subobjectSupport {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)]
    (P : Subobject (family k)) :
    subsetSubobject k (subobjectSupport k P) = P := sorry

/-- Inclusion of supports exactly detects the order on subobjects of a coproduct of field
spectra. -/
@[stacks 03DP]
theorem subobjectSupport_subset_iff {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)]
    (P Q : Subobject (family k)) :
    subobjectSupport k P ⊆ subobjectSupport k Q ↔ P ≤ Q := sorry

/-- Subobjects of a coproduct of field spectra are canonically classified by subsets of the
indexing type. -/
@[stacks 03DP "subobjects of a coproduct of field spectra"]
noncomputable def subobjectEquivSet {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)] :
    Subobject (family k) ≃o Set ι where
  toFun := subobjectSupport k
  invFun := subsetSubobject k
  left_inv := subsetSubobject_subobjectSupport k
  right_inv := subobjectSupport_subsetSubobject k
  map_rel_iff' := fun {P Q} => subobjectSupport_subset_iff k P Q

/-- The inverse of the coproduct-subobject classification sends a subset to its canonical
inclusion subobject. -/
@[simp, stacks 03DP]
theorem subobjectEquivSet_symm_apply {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)] (J : Set ι) :
    (subobjectEquivSet k).symm J = subsetSubobject k J := sorry

/-- Lemma 26.23.11 (2): a monomorphism into a coproduct of field spectra is the inclusion of a
subfamily up to isomorphism over the target. -/
@[stacks 03DP]
theorem exists_subset_isoOver_of_mono {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)]
    {Y : Scheme.{v}} (f : Y ⟶ family k) [Mono f] :
    ∃ J : Set ι, Nonempty (Over.mk f ≅ Over.mk (inclusion k J)) := sorry

/- The target-free companion is kept separate from the over-category statement so downstream
arguments can consume an ordinary scheme isomorphism without unpacking its map to `family k`. -/
/-- Forgetting the target map, a monomorphism into a coproduct of field spectra has source scheme
isomorphic to the coproduct indexed by a subfamily. -/
@[stacks 03DP "field-spectrum source isomorphism"]
theorem exists_subset_iso_of_mono {ι : Type u} [Small.{v} ι]
    (k : ι → Type v) [∀ i, Field (k i)]
    {Y : Scheme.{v}} (f : Y ⟶ family k) [Mono f] :
    ∃ J : Set ι, IsIsomorphic Y (subfamily k J) := sorry

end AlgebraicGeometry.Scheme.Coproduct.FieldSpectra
