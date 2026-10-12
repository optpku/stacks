/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.ObjectProperty.Small
import Mathlib.Tactic.CrossRefAttribute

/-!
# Small abelian full subcategories

This file packages a full subcategory of an abelian category whose objects are small and whose
inclusion is exact.  The exactness field is part of the owner: merely knowing that the induced full
subcategory is abelian does not say that its exact sequences agree with those in the ambient
category.
-/

@[expose] public section

open CategoryTheory Limits

universe i w v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A small abelian full subcategory of `A`, with exact inclusion into `A`.

Here `full` means that all ambient morphisms between selected objects are retained; it does not
mean `replete`.  This distinction is essential in a large category: adjoining every ambient object
isomorphic to a selected object need not preserve smallness. -/
@[stacks 05PQ "small abelian full subcategory"]
structure SmallAbelianSubcategory (A : Type u) [Category.{v} A] [Abelian A] where
  /-- The property selecting the objects of the full subcategory. -/
  carrier : ObjectProperty A
  /-- A model in `Type w` for the selected objects. -/
  objectModel : Type w
  /-- The selected objects are equivalent to their small model. -/
  equivObjectModel : Subtype carrier ≃ objectModel
  /-- The induced full subcategory is abelian. -/
  abelian : Abelian carrier.FullSubcategory
  /-- The inclusion into the ambient abelian category is exact. -/
  inclusionExact : exactFunctor carrier.FullSubcategory A carrier.ι

namespace SmallAbelianSubcategory

variable (B : SmallAbelianSubcategory.{w, v, u} A)

/-- The full subcategory selected by `B`. -/
abbrev FullSubcategory := B.carrier.FullSubcategory

/-- Containment of an object property in `B`. -/
protected def Contains (E : ObjectProperty A) : Prop := E ≤ B.carrier

/-- The carrier of a small abelian subcategory is small. -/
def smallCarrier : ObjectProperty.Small.{w} B.carrier :=
  Small.mk' B.equivObjectModel

/-- The full subcategory selected by `B` carries its specified abelian structure. -/
def abelianFullSubcategory : Abelian B.FullSubcategory := B.abelian

/-- An object property is contained in `B` exactly when it is pointwise bounded by the carrier. -/
@[simp]
theorem contains_iff (E : ObjectProperty A) : B.Contains E ↔ E ≤ B.carrier := sorry

/-- The inclusion of a small abelian subcategory preserves finite limits. -/
def inclusion_preservesFiniteLimits : PreservesFiniteLimits B.carrier.ι :=
  B.inclusionExact.1

/-- The inclusion of a small abelian subcategory preserves finite colimits. -/
def inclusion_preservesFiniteColimits : PreservesFiniteColimits B.carrier.ι :=
  B.inclusionExact.2

/-- The inclusion of a small abelian subcategory, bundled as an exact functor. -/
@[stacks 05PQ "exact inclusion"]
def inclusion : B.FullSubcategory ⥤ₑ A :=
  ⟨B.carrier.ι, B.inclusionExact⟩

/-- The exact inclusion sends an object to its underlying ambient object. -/
@[simp]
theorem inclusion_obj (X : B.FullSubcategory) :
    B.inclusion.obj.obj X = X.obj := sorry

/-- The exact inclusion sends a morphism to its underlying ambient morphism. -/
@[simp]
theorem inclusion_map {X Y : B.FullSubcategory} (f : X ⟶ Y) :
    B.inclusion.obj.map f = f.hom := sorry

/-- A short complex in a small abelian subcategory is short exact exactly when its image in the
ambient abelian category is short exact. -/
@[stacks 05PQ "short exact sequences under inclusion"]
theorem inclusion_shortExact_iff {S : ShortComplex B.FullSubcategory} :
    (S.map B.carrier.ι).ShortExact ↔ S.ShortExact := sorry

/-- The replete closure of the carrier remains essentially small.  It need not be small, since an
ambient isomorphism class can have a large type of representatives. -/
@[stacks 05PQ "replete closure"]
theorem essentiallySmall_isoClosure :
    ObjectProperty.EssentiallySmall.{w} B.carrier.isoClosure := sorry

/-- At any universe in which the ambient category is locally small, every small object property
is contained in a small abelian full subcategory. -/
@[stacks 05PQ "locally small universe"]
theorem exists_containingAt (E : ObjectProperty A) [ObjectProperty.Small.{w} E]
    [LocallySmall.{w} A] :
    ∃ B : SmallAbelianSubcategory.{w, v, u} A, B.Contains E := sorry

/-- Every small object property in an abelian category is contained in a small abelian full
subcategory.  The output universe also accommodates the ambient Hom types. -/
@[stacks 05PQ]
theorem exists_containing (E : ObjectProperty A) [ObjectProperty.Small.{w} E] :
    ∃ B : SmallAbelianSubcategory.{max v w, v, u} A, B.Contains E := sorry

/-- A set-sized family of objects lies in a small abelian full subcategory with exact inclusion. -/
theorem exists_containingFamily {I : Type i} [Small.{w} I] (X : I → A) :
    ∃ B : SmallAbelianSubcategory.{max v w, v, u} A, ∀ i, B.carrier (X i) := sorry

/-- Construct a small abelian subcategory from its object property, model, abelian structure,
and exact inclusion data. -/
def ofProperty (carrier : ObjectProperty A) (objectModel : Type w)
    (equivObjectModel : Subtype carrier ≃ objectModel)
    (abelian : Abelian carrier.FullSubcategory)
    (inclusionExact : exactFunctor carrier.FullSubcategory A carrier.ι) :
    SmallAbelianSubcategory.{w, v, u} A :=
  { carrier, objectModel, equivObjectModel, abelian, inclusionExact }

/-- The selected carrier is small and its inclusion into the ambient category is exact. -/
theorem spec : ObjectProperty.Small.{w} B.carrier ∧
    exactFunctor B.FullSubcategory A B.carrier.ι := sorry

end SmallAbelianSubcategory

end CategoryTheory
