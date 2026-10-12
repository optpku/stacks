/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

-- Import decisions:
-- * Locally-discrete sources, pseudofunctor bicategories, and `Grpd` occur in
--   the exported property and owner type.
-- * `Bicategory.Equivalence` supplies the invariant-closure API used by the
--   public instance below.
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import ReasLib.CategoryTheory.Bicategory.Equivalence
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Definition

/-!
# Groupoid-valued pseudofunctors

The invariant full subbicategory of `Cat`-valued pseudofunctors whose values
are groupoids. This is independent of any realization as a fibred category.
-/

@[expose] public section

universe wB vB uB w v₁ v₂ u

namespace CategoryTheory.Pseudofunctor

open scoped Bicategory Pseudofunctor.StrongTrans

/-- The invariant object property selecting `Cat`-valued pseudofunctors on an arbitrary source
bicategory whose values are groupoids. It is the property-level form of factoring through
`Grpd ↪ Cat` without choosing inverse operations. -/
abbrev isGroupoidValuedOn
    (B : Type uB) [Bicategory.{wB, vB} B] :
    ObjectProperty (B ⥤ᵖ Cat.{v₂, w}) :=
  fun F ↦ ∀ U, IsGroupoid (F.obj U)

/-- Pointwise groupoidality is preserved by equivalence of pseudofunctors on an arbitrary
source bicategory. -/
instance isGroupoidValuedOn.isClosedUnderEquivalences
    (B : Type uB) [Bicategory.{wB, vB} B] :
    (isGroupoidValuedOn B :
      ObjectProperty (B ⥤ᵖ Cat.{v₂, w})).IsClosedUnderEquivalences := sorry

set_option linter.checkUnivs false in
/-- The full subbicategory of `Cat`-valued pseudofunctors on `B` whose values are groupoids. -/
abbrev GroupoidValuedOn
    (B : Type uB) [Bicategory.{wB, vB} B] :=
  ((isGroupoidValuedOn B :
    ObjectProperty (B ⥤ᵖ Cat.{v₂, w}))).FullSubbicategory

namespace GroupoidValuedOn

/-- Package a pointwise groupoidal pseudofunctor on an arbitrary source bicategory as an owner
object of `GroupoidValuedOn`. -/
def mk
    {B : Type uB} [Bicategory.{wB, vB} B]
    (F : B ⥤ᵖ Cat.{v₂, w})
    [∀ U, IsGroupoid (F.obj U)] :
    ((isGroupoidValuedOn B :
      ObjectProperty (B ⥤ᵖ Cat.{v₂, w}))).FullSubbicategory :=
  ObjectProperty.FullSubbicategory.mk (isGroupoidValuedOn B) F (fun _ ↦ inferInstance)

/-- The underlying `Cat`-valued pseudofunctor of a general groupoid-valued owner object. -/
abbrev toPseudofunctor
    {B : Type uB} [Bicategory.{wB, vB} B]
    (F : Pseudofunctor.GroupoidValuedOn B) :=
  F.1

/-- The underlying pseudofunctor of `GroupoidValuedOn.mk F` is the original `F`. -/
@[simp]
theorem mk_toPseudofunctor
    {B : Type uB} [Bicategory.{wB, vB} B]
    (F : B ⥤ᵖ Cat.{v₂, w})
    [∀ U, IsGroupoid (F.obj U)] :
    GroupoidValuedOn.toPseudofunctor (mk F) = F := sorry

/-- A general groupoid-valued owner object has groupoidal values pointwise. -/
instance pointwiseIsGroupoid
    {B : Type uB} [Bicategory.{wB, vB} B]
    (F : Pseudofunctor.GroupoidValuedOn B) :
    ∀ U, IsGroupoid ((GroupoidValuedOn.toPseudofunctor F).obj U) := sorry

end GroupoidValuedOn

/-- The ordinary-base specialization of `isGroupoidValuedOn` for contravariant pseudofunctors.
It keeps the standard `[Cᵒᵖ, Grpd]` public surface while inheriting the arbitrary-bicategory
formalization. -/
abbrev isGroupoidValued (C : Type u) [Category.{v₁} C] :
    ObjectProperty (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v₂, w}) :=
  isGroupoidValuedOn (LocallyDiscrete Cᵒᵖ)

set_option linter.checkUnivs false in
/-- The canonical bicategory `[Cᵒᵖ, Grpd]`: `Cat`-valued pseudofunctors whose values are
groupoids, strong transformations, and modifications. Modeling this as a replete full
subbicategory records the invariant factorization through `Grpd ↪ Cat` without exposing a chosen
`Groupoid.ofIsGroupoid` structure at every value. -/
abbrev GroupoidValued (C : Type u) [Category.{v₁} C] :=
  ((isGroupoidValued C :
    ObjectProperty (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v₂, w}))).FullSubbicategory

namespace GroupoidValued

/-- Package a pointwise groupoidal `Cat`-valued pseudofunctor as an object of the canonical
groupoid-valued full subbicategory. The pseudofunctor is retained unchanged; the supplied
instances provide exactly the invariant membership proof. -/
def mk
    {C : Type u} [Category.{v₁} C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v₂, w})
    [∀ U, IsGroupoid (F.obj U)] :
    Pseudofunctor.GroupoidValued C :=
  GroupoidValuedOn.mk F

/-- The underlying `Cat`-valued pseudofunctor of a groupoid-valued owner object. This stable
high-frequency projection avoids exposing the raw `.1` projection in downstream APIs. -/
abbrev toPseudofunctor
    {C : Type u} [Category.{v₁} C] (F : Pseudofunctor.GroupoidValued C) :=
  F.1

/-- The underlying pseudofunctor of `GroupoidValued.mk F` is the original `F`. -/
@[simp]
theorem mk_toPseudofunctor
    {C : Type u} [Category.{v₁} C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v₂, w})
    [∀ U, IsGroupoid (F.obj U)] :
    (mk F).toPseudofunctor = F := sorry

/-- A groupoid-valued pseudofunctor carries the canonical pointwise `IsGroupoid` instances.
This projection instance lets downstream constructions consume the invariant object property
without repeatedly reinstalling `F.property` at each use site.

Proof strategy: this is exactly the property projection `F.property`. -/
instance pointwiseIsGroupoid
    {C : Type u} [Category.{v₁} C] (F : Pseudofunctor.GroupoidValued C) :
    ∀ U, IsGroupoid (F.toPseudofunctor.obj U) := sorry

end GroupoidValued

end CategoryTheory.Pseudofunctor
