module

public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Domain

@[expose] public section

/-!
# Essential-Constancy Domains for Pointwise Derived Functors

Stacks' source notion of a derived functor being defined retains an essentially constant
localization-indexed diagram.  This leaf packages that stronger predicate as an object property
and a full subcategory, and provides canonical inclusions into Mathlib's weaker pointwise-existence
domains.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open ObjectProperty

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)

/-- The object property where the right-derived indexing diagram is essentially constant.  This
is stronger than `Functor.RightDerived.Definedness.property`, which records only pointwise existence. -/
@[stacks 05SC "essential-constancy domain of a right derived functor"]
abbrev Functor.RightDerived.DefinedAt.objects : ObjectProperty D :=
  fun X ↦ Functor.RightDerived.DefinedAt F S X

/-- The object property where the left-derived indexing diagram is essentially constant.  This is
stronger than `Functor.LeftDerived.Definedness.property`, which records only pointwise existence. -/
@[stacks 05SC "essential-constancy domain of a left derived functor"]
abbrev Functor.LeftDerived.DefinedAt.objects : ObjectProperty D :=
  fun X ↦ Functor.LeftDerived.DefinedAt F S X

/-- Right-derived essential constancy is invariant under isomorphisms of source objects. -/
instance Functor.RightDerived.DefinedAt.closedUnderIso :
    (Functor.RightDerived.DefinedAt.objects F S).IsClosedUnderIsomorphisms := sorry

/-- Left-derived essential constancy is invariant under isomorphisms of source objects. -/
instance Functor.LeftDerived.DefinedAt.closedUnderIso :
    (Functor.LeftDerived.DefinedAt.objects F S).IsClosedUnderIsomorphisms := sorry

/-- The full subcategory on which the right-derived indexing diagram is essentially constant. -/
@[stacks 05SC "essential-constancy subcategory for right derived values"]
abbrev Functor.RightDerived.DefinedAt.Domain :=
  (Functor.RightDerived.DefinedAt.objects F S).FullSubcategory

/-- The full subcategory on which the left-derived indexing diagram is essentially constant. -/
@[stacks 05SC "essential-constancy subcategory for left derived values"]
abbrev Functor.LeftDerived.DefinedAt.Domain :=
  (Functor.LeftDerived.DefinedAt.objects F S).FullSubcategory

/-- An object of the right essential-constancy subcategory automatically supplies the stronger
source-definedness instance. -/
instance Functor.RightDerived.DefinedAt.Domain.definedAt
    (X : Functor.RightDerived.DefinedAt.Domain F S) :
    Functor.RightDerived.DefinedAt F S X.obj := X.property

/-- An object of the left essential-constancy subcategory automatically supplies the stronger
source-definedness instance. -/
instance Functor.LeftDerived.DefinedAt.Domain.definedAt
    (X : Functor.LeftDerived.DefinedAt.Domain F S) :
    Functor.LeftDerived.DefinedAt F S X.obj := X.property

/-- Essential constancy of the right-derived diagram implies Mathlib's pointwise-existence
property. -/
theorem Functor.RightDerived.DefinedAt.lePointwise :
    Functor.RightDerived.DefinedAt.objects F S ≤
      Functor.RightDerived.Definedness.property F S := sorry

/-- Essential constancy of the left-derived diagram implies Mathlib's pointwise-existence
property. -/
theorem Functor.LeftDerived.DefinedAt.lePointwise :
    Functor.LeftDerived.DefinedAt.objects F S ≤
      Functor.LeftDerived.Definedness.property F S := sorry

/-- The canonical inclusion from the right essential-constancy domain into the pointwise-defined
domain.  It retains the underlying object and morphism. -/
def Functor.RightDerived.DefinedAt.Domain.toPointwise :
    Functor.RightDerived.DefinedAt.Domain F S ⥤ Functor.RightDerived.Definedness.Domain F S :=
  (Functor.RightDerived.DefinedAt.objects F S).ιOfLE
    (Functor.RightDerived.DefinedAt.lePointwise F S)

/-- The canonical inclusion from the left essential-constancy domain into the pointwise-defined
domain.  It retains the underlying object and morphism. -/
def Functor.LeftDerived.DefinedAt.Domain.toPointwise :
    Functor.LeftDerived.DefinedAt.Domain F S ⥤ Functor.LeftDerived.Definedness.Domain F S :=
  (Functor.LeftDerived.DefinedAt.objects F S).ιOfLE
    (Functor.LeftDerived.DefinedAt.lePointwise F S)

namespace Functor.RightDerived.DefinedAt.Domain.toPointwise

/-- The right-domain inclusion does not change the underlying source object. -/
@[simp]
theorem obj_obj (X : Functor.RightDerived.DefinedAt.Domain F S) :
    ((Functor.RightDerived.DefinedAt.Domain.toPointwise F S).obj X).obj = X.obj := sorry

/-- The right-domain inclusion retains the underlying source morphism. -/
@[simp]
theorem map_hom
    {X Y : Functor.RightDerived.DefinedAt.Domain F S} (f : X ⟶ Y) :
    ((Functor.RightDerived.DefinedAt.Domain.toPointwise F S).map f).hom = f.hom := sorry

end Functor.RightDerived.DefinedAt.Domain.toPointwise

namespace Functor.LeftDerived.DefinedAt.Domain.toPointwise

/-- The left-domain inclusion does not change the underlying source object. -/
@[simp]
theorem obj_obj (X : Functor.LeftDerived.DefinedAt.Domain F S) :
    ((Functor.LeftDerived.DefinedAt.Domain.toPointwise F S).obj X).obj = X.obj := sorry

/-- The left-domain inclusion retains the underlying source morphism. -/
@[simp]
theorem map_hom
    {X Y : Functor.LeftDerived.DefinedAt.Domain F S} (f : X ⟶ Y) :
    ((Functor.LeftDerived.DefinedAt.Domain.toPointwise F S).map f).hom = f.hom := sorry

end Functor.LeftDerived.DefinedAt.Domain.toPointwise



end CategoryTheory
