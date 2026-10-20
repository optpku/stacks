module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.ObjectProperty.Over.Basic

/-!
# Etale commutative algebras over a fixed target

This leaf owns the category of etale commutative `R`-algebras equipped with an
`R`-algebra map to a fixed target.  It is independent of a chosen prime,
residue field, or henselization.

@stack 04GV
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace CommAlgCat.Over.Etale

/-- The object property on `Over (CommAlgCat.of R T)` selecting the algebras
that are etale over `R`. -/
@[stacks 04GV "etale algebras over a target"]
abbrev property (R : Type u) [CommRing R]
    (T : Type v) [CommRing T] [Algebra R T] :
    ObjectProperty (CategoryTheory.Over (CommAlgCat.of R T)) :=
  fun A => RingHom.Etale (algebraMap R A.left)

/-- The category of etale `R`-algebras equipped with a map to the target
`R`-algebra `T`. -/
@[stacks 04GV "pointed etale algebra category"]
abbrev category (R : Type u) [CommRing R]
    (T : Type v) [CommRing T] [Algebra R T] :=
  (property R T).FullSubcategory

/-- The diagram of etale `R`-algebras over `T`, after forgetting their maps to
`T`. -/
@[stacks 04GV "pointed etale algebra diagram"]
abbrev diagram (R : Type u) [CommRing R]
    (T : Type v) [CommRing T] [Algebra R T] :=
  CategoryTheory.ObjectProperty.Over.forgetDiagram (property R T)

/-- The canonical cocone from etale `R`-algebras over `T` to `T`. -/
@[stacks 04GV "pointed etale algebra cocone"]
abbrev cocone (R : Type u) [CommRing R]
    (T : Type v) [CommRing T] [Algebra R T] :=
  CategoryTheory.ObjectProperty.Over.forgetCocone (property R T)

section Witnesses

variable {R : Type u} [CommRing R]
variable {T : Type v} [CommRing T] [Algebra R T]

/-- The base algebra, transported to the carrier universe of the pointed category.
The size premise is needed only to supply this nonempty object. -/
@[stacks 04GV "base pointed etale algebra"]
noncomputable def base (R : Type u) [CommRing R]
    (T : Type v) [CommRing T] [Algebra R T] [Small.{v} R] : category R T where
  obj := Over.mk (CommAlgCat.ofHom
    ((Algebra.ofId R T).comp (Shrink.algEquiv R R).toAlgHom))
  property := by
    exact RingHom.Etale.of_bijective (Shrink.algEquiv R R).symm.bijective

/-- The tensor product of two pointed etale algebras, pointed by multiplying
their two images in the common target. -/
@[stacks 04GV "tensor product of pointed etale algebras"]
noncomputable def tensorObj (A B : category R T) : category R T where
  obj := Over.mk (CommAlgCat.ofHom
    (Algebra.TensorProduct.lift A.obj.hom.hom B.obj.hom.hom
      (fun _ _ ↦ Commute.all _ _)))
  property := by
    letI : Algebra.Etale R A.obj.left := (RingHom.etale_algebraMap).mp A.property
    letI : Algebra.Etale R B.obj.left := (RingHom.etale_algebraMap).mp B.property
    exact (RingHom.etale_algebraMap).mpr
      (Algebra.Etale.comp R A.obj.left (A.obj.left ⊗[R] B.obj.left))

/-- The first factor maps to the common pointed tensor product by `a ↦ a ⊗ 1`. -/
noncomputable def tensorInl (A B : category R T) : A ⟶ tensorObj A B :=
  ObjectProperty.homMk (Over.homMk
    (CommAlgCat.ofHom Algebra.TensorProduct.includeLeft) (by sorry))

/-- The second factor maps to the common pointed tensor product by `b ↦ 1 ⊗ b`. -/
noncomputable def tensorInr (A B : category R T) : B ⟶ tensorObj A B :=
  ObjectProperty.homMk (Over.homMk
    (CommAlgCat.ofHom Algebra.TensorProduct.includeRight) (by sorry))

/-- The ideal enforcing equality of two parallel pointed algebra maps. -/
def coequalizerIdeal {A B : category R T} (f g : A ⟶ B) : Ideal B.obj.left :=
  Ideal.span (Set.range fun a : A.obj.left ↦ f.hom.left.hom a - g.hom.left.hom a)

/-- The target map descends through the difference ideal because both maps
are morphisms over the same target. -/
noncomputable def coequalizerTargetMap {A B : category R T} (f g : A ⟶ B) :
    B.obj.left ⧸ coequalizerIdeal f g →ₐ[R] T :=
  Ideal.Quotient.liftₐ (coequalizerIdeal f g) B.obj.hom.hom (by sorry)

/-- Quotienting by the differences of two parallel maps gives a pointed
etale algebra. This is the algebraic coequalizer underlying the tensor
construction in Tag 04GV. -/
@[stacks 04GV "coequalizing pointed etale algebra"]
noncomputable def coequalizerObj {A B : category R T} (f g : A ⟶ B) :
    category R T where
  obj := Over.mk (CommAlgCat.ofHom (coequalizerTargetMap f g))
  property := by
    sorry

/-- The canonical quotient map to the pointed coequalizing algebra. -/
noncomputable def coequalizerπ {A B : category R T} (f g : A ⟶ B) :
    B ⟶ coequalizerObj f g :=
  ObjectProperty.homMk (Over.homMk
    (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R (coequalizerIdeal f g))) (by sorry))

/-- The quotient map coequalizes the original parallel maps. -/
theorem coequalizer_condition {A B : category R T} (f g : A ⟶ B) :
    f ≫ coequalizerπ f g = g ≫ coequalizerπ f g := sorry

/-- The base point is the structural algebra map after undoing the universe transport. -/
@[simp]
theorem base_hom_apply [Small.{v} R] (r : Shrink.{v} R) :
    (base R T).obj.hom.hom r = algebraMap R T (Shrink.algEquiv R R r) := rfl

/-- The tensor point sends a pure tensor to the product of its two images. -/
@[simp]
theorem tensorObj_hom_tmul (A B : category R T) (a : A.obj.left) (b : B.obj.left) :
    (tensorObj A B).obj.hom.hom (a ⊗ₜ[R] b) = A.obj.hom.hom a * B.obj.hom.hom b := rfl

/-- The left cocone map is the standard left tensor inclusion. -/
@[simp]
theorem tensorInl_apply (A B : category R T) (a : A.obj.left) :
    (tensorInl A B).hom.left.hom a = a ⊗ₜ[R] (1 : B.obj.left) := rfl

/-- The right cocone map is the standard right tensor inclusion. -/
@[simp]
theorem tensorInr_apply (A B : category R T) (b : B.obj.left) :
    (tensorInr A B).hom.left.hom b = (1 : A.obj.left) ⊗ₜ[R] b := rfl

/-- The coequalizing map takes an element to its quotient class. -/
@[simp]
theorem coequalizerπ_apply {A B : category R T} (f g : A ⟶ B) (b : B.obj.left) :
    (coequalizerπ f g).hom.left.hom b = Ideal.Quotient.mk (coequalizerIdeal f g) b := rfl

/-- The point of the coequalizing algebra is induced by the original target map. -/
@[simp]
theorem coequalizerTargetMap_mk {A B : category R T} (f g : A ⟶ B) (b : B.obj.left) :
    coequalizerTargetMap f g (Ideal.Quotient.mk (coequalizerIdeal f g) b) =
      B.obj.hom.hom b := rfl

/-- Tensor products and difference quotients supply the two finite-diagram
conditions without any size assumption on the base ring. -/
instance instIsFilteredOrEmpty : IsFilteredOrEmpty (category R T) where
  cocone_objs A B := ⟨tensorObj A B, tensorInl A B, tensorInr A B, trivial⟩
  cocone_maps _ _ f g := ⟨coequalizerObj f g, coequalizerπ f g, coequalizer_condition f g⟩

end Witnesses

/-- Etale `R`-algebras equipped with a map to any fixed commutative-ring target
form a filtered category when the base ring fits the carrier universe.

The `Small` premise supplies the base object; it is automatic when the base
and target are in the same universe, as in the source.

The field-valued specialization is the source-facing presentation by a chosen
point (and, at a residue field, by a prime with the corresponding residue-field
map).  Keeping the target only as a commutative ring makes this owner reusable
for arbitrary affine base changes and avoids baking the geometric
specialization into the category itself. -/
@[stacks 04GV "filtered pointed etale algebras"]
theorem isFiltered {R : Type u} [CommRing R]
    {T : Type v} [CommRing T] [Algebra R T] [Small.{v} R] :
    IsFiltered (category R T) where
  nonempty := ⟨base R T⟩

/-- Typeclass form of `isFiltered` for the canonical pointed etale category. -/
@[stacks 04GV "filtered pointed etale algebras"]
instance instIsFiltered {R : Type u} [CommRing R]
    {T : Type v} [CommRing T] [Algebra R T] [Small.{v} R] :
    IsFiltered (category R T) := isFiltered

end CommAlgCat.Over.Etale
