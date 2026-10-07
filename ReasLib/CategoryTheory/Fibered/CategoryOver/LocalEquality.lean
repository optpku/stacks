module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Cleavage
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber
public import ReasLib.CategoryTheory.Fibered.Cleavage.LocalEquality

/-!
# Local-equality quotients of fibred categories

`Functor.Cleavage.LocalEquality` owns the cleavage-explicit relation and its
canonical mathlib quotient category.  This module only fixes the standard
chosen cleavage of a bundled `FiberedCategoryOver`, then packages the quotient
functor as a morphism of fibred categories.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver

namespace LocalEquality

/-- The selected-cleavage specialization of local equality for a bundled fibred category. -/
noncomputable abbrev locallyEqual (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) {x y : X.total} (f g : x ⟶ y) : Prop :=
  Functor.Cleavage.LocalEquality.locallyEqual J (X.chosenCleavage) f g

/-- The selected-cleavage specialization of the strict-equality restriction sieve. -/
noncomputable abbrev equalRestrictionSieve (X : FiberedCategoryOver.{u, v, w, vS} C)
    {x y : X.total} (f g : x ⟶ y) : Sieve (X.p.obj x) :=
  Functor.Cleavage.LocalEquality.equalRestrictionSieve (X.chosenCleavage) f g

/-- Selected-cleavage local equality is characterized by its strict-equality restriction sieve. -/
theorem locallyEqual_iff_equalRestrictionSieve_mem
    (J : GrothendieckTopology C) (X : FiberedCategoryOver.{u, v, w, vS} C)
    {x y : X.total} (f g : x ⟶ y) :
    locallyEqual J X f g ↔
      X.p.map f = X.p.map g ∧ equalRestrictionSieve X f g ∈ J (X.p.obj x) := sorry

/-- The selected-cleavage local-equality criterion in the covering-family form used by source
constructions. -/
theorem locallyEqual_iff_exists_cover
    (J : GrothendieckTopology C) (X : FiberedCategoryOver.{u, v, w, vS} C)
    {x y : X.total} (f g : x ⟶ y) :
    locallyEqual J X f g ↔
      X.p.map f = X.p.map g ∧
        ∃ R : J.Cover (X.p.obj x), ∀ I : R.Arrow,
          (X.chosenCleavage).cartesianHom I.f
              (Functor.Fiber.mk (p := X.p) (a := x) rfl) ≫ f =
            (X.chosenCleavage).cartesianHom I.f
              (Functor.Fiber.mk (p := X.p) (a := x) rfl) ≫ g := sorry

/-- The local-equality Hom relation on the total category of a bundled fibred category. -/
noncomputable abbrev homRel (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) : HomRel X.total :=
  Functor.Cleavage.LocalEquality.homRel J (X.chosenCleavage)

/-- The selected-cleavage Hom relation is exactly the selected local-equality predicate. -/
@[simp]
theorem homRel_iff (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) {x y : X.total} (f g : x ⟶ y) :
    homRel J X f g ↔ locallyEqual J X f g := sorry

/-- The local-equality quotient category of a bundled fibred category.  Its canonical owner is
`CategoryTheory.Quotient (homRel J X)`. -/
noncomputable abbrev QuotientTotal (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) :=
  Functor.Cleavage.LocalEquality.QuotientTotal J (X.chosenCleavage)

namespace QuotientTotal

/-- The objects of the selected-cleavage local-equality quotient are canonically the objects of
the original total category. -/
noncomputable abbrev objectEquiv (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) : QuotientTotal J X ≃ X.total :=
  Functor.Cleavage.LocalEquality.QuotientTotal.objectEquiv J (X.chosenCleavage)

/-- The quotient object represented by an original total-category object. -/
noncomputable abbrev ofObj (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) (x : X.total) : QuotientTotal J X :=
  Functor.Cleavage.LocalEquality.QuotientTotal.ofObj J (X.chosenCleavage) x

/-- The selected-cleavage local-equality class of a total-category morphism. -/
noncomputable abbrev homMk (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) {x y : X.total} (f : x ⟶ y) :
    ofObj J X x ⟶ ofObj J X y :=
  Functor.Cleavage.LocalEquality.QuotientTotal.homMk J (X.chosenCleavage) f

/-- Equality of selected-cleavage quotient representatives is equivalent to local equality. -/
theorem homMk_eq_iff_locallyEqual (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) {x y : X.total} {f g : x ⟶ y} :
    homMk J X f = homMk J X g ↔ locallyEqual J X f g := sorry

/-- Equality of selected-cleavage quotient representatives is equivalently equality of base maps
and coverage of the strict-equality restriction sieve. -/
theorem homMk_eq_iff_equalRestrictionSieve_mem
    (J : GrothendieckTopology C) (X : FiberedCategoryOver.{u, v, w, vS} C)
    {x y : X.total} {f g : x ⟶ y} :
    homMk J X f = homMk J X g ↔
      X.p.map f = X.p.map g ∧ equalRestrictionSieve X f g ∈ J (X.p.obj x) := sorry

/-- A covering strict-equality restriction sieve identifies two selected-cleavage quotient
representatives. -/
theorem homMk_eq_of_equalRestrictionSieve_mem
    (J : GrothendieckTopology C) (X : FiberedCategoryOver.{u, v, w, vS} C)
    {x y : X.total} {f g : x ⟶ y}
    (hbase : X.p.map f = X.p.map g)
    (hcover : equalRestrictionSieve X f g ∈ J (X.p.obj x)) :
    homMk J X f = homMk J X g := sorry

/-- Quotient representatives agree when their cartesian restrictions agree over a covering
family. -/
theorem homMk_eq_of_cover_eq (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) {x y : X.total} {f g : x ⟶ y}
    (hbase : X.p.map f = X.p.map g)
    (R : J.Cover (X.p.obj x))
    (hR : ∀ I : R.Arrow,
      homMk J X
          ((X.chosenCleavage).cartesianHom I.f
              (Functor.Fiber.mk (p := X.p) (a := x) rfl) ≫ f) =
        homMk J X
          ((X.chosenCleavage).cartesianHom I.f
              (Functor.Fiber.mk (p := X.p) (a := x) rfl) ≫ g)) :
    homMk J X f = homMk J X g := sorry

/-- Local equality follows when quotient representatives agree after cartesian restriction over
a covering family. -/
theorem locallyEqual_of_cover_eq (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) {x y : X.total} {f g : x ⟶ y}
    (hbase : X.p.map f = X.p.map g)
    (R : J.Cover (X.p.obj x))
    (hR : ∀ I : R.Arrow,
      homMk J X
          ((X.chosenCleavage).cartesianHom I.f
              (Functor.Fiber.mk (p := X.p) (a := x) rfl) ≫ f) =
        homMk J X
          ((X.chosenCleavage).cartesianHom I.f
              (Functor.Fiber.mk (p := X.p) (a := x) rfl) ≫ g)) :
    locallyEqual J X f g := sorry

/-- The canonical projection from the selected-cleavage quotient category to the base. -/
noncomputable abbrev projection (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) : QuotientTotal J X ⥤ C :=
  Functor.Cleavage.LocalEquality.QuotientTotal.projection J (X.chosenCleavage)

/-- The selected-cleavage projection sends a representative to its original base map. -/
@[simp]
theorem projection_map_homMk (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) {x y : X.total} (f : x ⟶ y) :
    (projection J X).map (homMk J X f) = X.p.map f := sorry

/-- A strongly cartesian representative remains strongly cartesian in the selected-cleavage
quotient over any displayed base arrow for which it is a strongly cartesian lift. -/
theorem homMk_isStronglyCartesian (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C)
    {U V : C} {q : U ⟶ V} {x y : X.total} (φ : x ⟶ y)
    (hφ : X.p.IsStronglyCartesian q φ) :
    (projection J X).IsStronglyCartesian q (homMk J X φ) := sorry

/-- Quotient morphisms are equal when their base maps agree and their precomposites by the
chosen cartesian arrows of a cover are equal. -/
theorem eq_of_cover_comp_homMk_eq (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) {x y : X.total}
    (a b : ofObj J X x ⟶ ofObj J X y)
    (hbase : (projection J X).map a = (projection J X).map b)
    (R : J.Cover (X.p.obj x))
    (hR : ∀ I : R.Arrow,
      homMk J X
          ((X.chosenCleavage).cartesianHom I.f
              (Functor.Fiber.mk (p := X.p) (a := x) rfl)) ≫ a =
        homMk J X
          ((X.chosenCleavage).cartesianHom I.f
              (Functor.Fiber.mk (p := X.p) (a := x) rfl)) ≫ b) :
    a = b := sorry

/-- Quotient morphisms are equal when they agree after precomposition by any strongly cartesian
testing family over a cover. -/
theorem eq_of_cover_comp_stronglyCartesian
    (J : GrothendieckTopology C) (X : FiberedCategoryOver.{u, v, w, vS} C)
    {x y : X.total} (a b : ofObj J X x ⟶ ofObj J X y)
    (hbase : (projection J X).map a = (projection J X).map b)
    (R : J.Cover (X.p.obj x))
    (w' : R.Arrow → QuotientTotal J X)
    (φ : ∀ I : R.Arrow, w' I ⟶ ofObj J X x)
    (hφ : ∀ I : R.Arrow, (projection J X).IsStronglyCartesian I.f (φ I))
    (hR : ∀ I : R.Arrow, φ I ≫ a = φ I ≫ b) :
    a = b := sorry

/-- Fiber morphisms of the selected-cleavage quotient are equal when a covering strongly
cartesian testing family makes their underlying composites equal. -/
theorem fiberHom.eq_of_cover_comp_stronglyCartesian
    (J : GrothendieckTopology C) (X : FiberedCategoryOver.{u, v, w, vS} C) {U : C}
    {x y : (projection J X).Fiber U} (a b : x ⟶ y)
    (R : J.Cover U)
    (w' : R.Arrow → QuotientTotal J X)
    (φ : ∀ I : R.Arrow, w' I ⟶ x.1)
    (hφ : ∀ I : R.Arrow, (projection J X).IsStronglyCartesian I.f (φ I))
    (hR : ∀ I : R.Arrow, φ I ≫ a.1 = φ I ≫ b.1) :
    a = b := sorry

/-- A named selected-cleavage proof that the quotient projection is fibred.  Typeclass search
uses the underlying cleavage-explicit instance. -/
noncomputable abbrev projectionIsFibered (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) : (projection J X).IsFibered :=
  Functor.Cleavage.LocalEquality.QuotientTotal.projectionIsFibered J (X.chosenCleavage)

/-- The canonical quotient functor from the original total category. -/
noncomputable abbrev quotientFunctor (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) : X.total ⥤ QuotientTotal J X :=
  Functor.Cleavage.LocalEquality.QuotientTotal.quotientFunctor J (X.chosenCleavage)

/-- The selected-cleavage quotient functor commutes with the original projection to the base. -/
theorem quotientFunctor_comp_projection (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) :
    quotientFunctor J X ⋙ projection J X = X.p := sorry

/-- Equality of maps under the selected-cleavage quotient functor is exactly local equality. -/
theorem quotientFunctor_map_eq_iff_locallyEqual (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) {x y : X.total} {f g : x ⟶ y} :
    (quotientFunctor J X).map f = (quotientFunctor J X).map g ↔ locallyEqual J X f g := sorry

/-- The selected-cleavage quotient regarded as a bundled fibred category over the base. -/
noncomputable def fiberedCategory (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) : FiberedCategoryOver.{u, v, w, vS} C :=
  FiberedCategoryOver.ofFunctor (projection J X)

/-- The projection of `fiberedCategory` is the selected-cleavage quotient projection. -/
@[simp]
theorem fiberedCategory_p (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) :
    (fiberedCategory J X).p = projection J X := sorry

/-- The quotient functor commutes with the projection of the bundled quotient fibred category. -/
theorem quotientFunctor_comp_fiberedCategory_p (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) :
    quotientFunctor J X ⋙ (fiberedCategory J X).p = X.p := sorry

/-- The selected-cleavage quotient functor as a based functor over the base. -/
noncomputable def basedFunctor (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) :
    X.toBasedCategory ⥤ᵇ (fiberedCategory J X).toBasedCategory where
  toFunctor := quotientFunctor J X
  w := quotientFunctor_comp_fiberedCategory_p J X

/-- The selected-cleavage quotient based functor preserves strongly cartesian morphisms. -/
theorem basedFunctor_preservesStronglyCartesian (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) :
    (basedFunctor J X).PreservesStronglyCartesian := sorry

/-- The canonical morphism of fibred categories from a fibred category to its selected-cleavage
local-equality quotient. -/
noncomputable def toFiberedCategory (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) : X ⟶ fiberedCategory J X :=
  FiberedCategoryOver.ofBasedFunctor
    (basedFunctor J X)
    (basedFunctor_preservesStronglyCartesian J X)

/-- The canonical quotient morphism sends a fiber arrow to its local-equality class. -/
@[simp]
theorem toFiberedCategory_fiberFunctor_map_val (J : GrothendieckTopology C)
    (X : FiberedCategoryOver.{u, v, w, vS} C) {U : C} {x y : X.p.Fiber U} (f : x ⟶ y) :
    ((FiberedCategoryOver.fiberFunctor (toFiberedCategory J X) U).map f).1 = homMk J X f.1 :=
  sorry

end QuotientTotal

end LocalEquality

end FiberedCategoryOver

end CategoryTheory
