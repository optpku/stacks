module

public import ReasLib.SetTheory.Cardinal.LowerInitialSegment
public import ReasLib.CategoryTheory.Abelian.QuotientRepresentatives
public import ReasLib.CategoryTheory.Generator.Subobject
public import ReasLib.CategoryTheory.Subobject.Cardinal

@[expose] public section

/-!
# Objects with Bounded Subobject Cardinality

A separator presents an object with bounded subobject lattice as a quotient of a bounded
coproduct.  Combining all lower-universe coproduct sizes with quotient representatives gives a
small family covering every such object up to isomorphism.
-/

open CategoryTheory.Limits

universe w v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-- The object property of having at most `kappa` subobjects. -/
@[stacks 079E "bounded subobject cardinal"]
def subobjectCardinalLE (kappa : Cardinal.{max u v}) : ObjectProperty C :=
  fun M ↦ Cardinal.mk (Subobject M) ≤ kappa

namespace SubobjectCardinal

/-- Membership in `subobjectCardinalLE kappa` is the corresponding cardinal inequality. -/
theorem mem_le_iff (kappa : Cardinal.{max u v}) (M : C) :
    subobjectCardinalLE kappa M ↔ Cardinal.mk (Subobject M) ≤ kappa := sorry

/-- Bounded subobject cardinality is invariant under isomorphisms. -/
instance closed_le (kappa : Cardinal.{max u v}) :
    (subobjectCardinalLE (C := C) kappa).IsClosedUnderIsomorphisms := sorry

end SubobjectCardinal
end CategoryTheory.ObjectProperty

namespace CategoryTheory.IsSeparator

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {U : C}

/-- A separator presents every object with bounded subobject cardinality as an epimorphic image
of at most that many copies of the separator. -/
@[stacks 079E "bounded coproduct quotient"]
theorem existsEpiFromCoproduct (hU : IsSeparator U) [HasCoproducts.{max u v} C]
    (M : C) (kappa : Cardinal.{max u v})
    (hM : ObjectProperty.subobjectCardinalLE kappa M) :
    ∃ (alpha : Type (max u v)) (_ : Cardinal.mk alpha ≤ kappa)
      (f : (∐ fun _ : alpha ↦ U) ⟶ M), Epi f := sorry

end CategoryTheory.IsSeparator

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Quotient representatives of all coproducts of `U` indexed by lower-universe cardinals
bounded by `kappa`. -/
@[stacks 079E "bounded separator quotients"]
noncomputable def boundedSeparatorQuotients [HasCoproducts.{w} C]
    (U : C) (kappa : Cardinal.{max u v}) : ObjectProperty C :=
  ObjectProperty.quotientRepresentatives
    (fun c : Cardinal.LowerInitialSegment.{w, max u v} kappa ↦
      ∐ fun _ : c.1.out ↦ U)

namespace BoundedSeparatorQuotients

variable [HasCoproducts.{w} C]

/-- Bounded separator quotients form a small object property in a well-powered category. -/
instance small [LocallySmall.{w} C] [WellPowered.{w} C]
    (U : C) (kappa : Cardinal.{max u v}) [Small.{w} kappa.out] :
    ObjectProperty.Small.{w} (boundedSeparatorQuotients U kappa) := sorry

/-- Every object of bounded subobject cardinality belongs to the iso-closure of the bounded
quotients of a separator. -/
theorem memIsoClosure {U M : C} (hU : IsSeparator U) [Small.{w} (Subobject M)]
    {kappa : Cardinal.{max u v}}
    (hM : ObjectProperty.subobjectCardinalLE kappa M) :
    (boundedSeparatorQuotients U kappa).isoClosure M := sorry

end BoundedSeparatorQuotients

namespace ObjectProperty.SubobjectCardinal

/-- In a well-powered abelian category with the relevant coproducts, a separator makes the
objects of bounded subobject cardinality essentially small. -/
theorem essentiallySmall_le_of_separator [HasCoproducts.{w} C]
    [LocallySmall.{w} C] [WellPowered.{w} C]
    (U : C) (hU : IsSeparator U) (kappa : Cardinal.{max u v})
    [Small.{w} kappa.out] :
    ObjectProperty.EssentiallySmall.{w}
      (ObjectProperty.subobjectCardinalLE (C := C) kappa) := sorry

end ObjectProperty.SubobjectCardinal

end CategoryTheory
