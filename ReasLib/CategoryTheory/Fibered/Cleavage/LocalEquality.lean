/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Quotient.LocallySmall
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso

/-!
# Local equality relative to a cleavage

This module owns the site-local relation on morphisms of a category fibred over
a site.  The quotient category itself is mathlib's `CategoryTheory.Quotient`:
the local construction supplies a `HomRel`, proves it is a `Congruence`, and
then uses the canonical quotient functor and its universal factorization API.
Mathlib's quotient-local-smallness instance is re-exported, so size-sensitive
consumers do not need to rebuild smallness separately for this quotient.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {S : Type uS} [Category.{vS} S]
variable {p : S ⥤ C}

namespace Functor.Cleavage

namespace LocalEquality

/-- Equality after restriction is closed under a further base restriction. -/
theorem equalRestrictionSieve_downward_closed (χ : p.Cleavage) {x y : S} (f g : x ⟶ y)
    {Y Z : C} {q : Y ⟶ p.obj x}
    (hq :
      χ.cartesianHom q (Functor.Fiber.mk (p := p) (a := x) rfl) ≫ f =
        χ.cartesianHom q (Functor.Fiber.mk (p := p) (a := x) rfl) ≫ g)
    (r : Z ⟶ Y) :
    χ.cartesianHom (r ≫ q) (Functor.Fiber.mk (p := p) (a := x) rfl) ≫ f =
      χ.cartesianHom (r ≫ q) (Functor.Fiber.mk (p := p) (a := x) rfl) ≫ g := sorry

/-- The sieve of base arrows along which two morphisms become equal after cartesian restriction
for a specified cleavage. -/
def equalRestrictionSieve (χ : p.Cleavage) {x y : S} (f g : x ⟶ y) : Sieve (p.obj x) where
  arrows _ q :=
    χ.cartesianHom q (Functor.Fiber.mk (p := p) (a := x) rfl) ≫ f =
      χ.cartesianHom q (Functor.Fiber.mk (p := p) (a := x) rfl) ≫ g
  downward_closed := fun hq r => equalRestrictionSieve_downward_closed χ f g hq r

/-- Two total-category morphisms are locally equal relative to a cleavage when they have the
same base map and their strict-equality restriction sieve is covering. -/
def locallyEqual (J : GrothendieckTopology C) (χ : p.Cleavage)
    {x y : S} (f g : x ⟶ y) : Prop :=
  p.map f = p.map g ∧ equalRestrictionSieve χ f g ∈ J (p.obj x)

/-- The sieve formulation of local equality.  This is the canonical site-theoretic definition. -/
theorem locallyEqual_iff_equalRestrictionSieve_mem
    (J : GrothendieckTopology C) (χ : p.Cleavage) {x y : S} (f g : x ⟶ y) :
    locallyEqual J χ f g ↔
      p.map f = p.map g ∧ equalRestrictionSieve χ f g ∈ J (p.obj x) := sorry

/-- The covering-family form of local equality used in the source construction. -/
theorem locallyEqual_iff_exists_cover
    (J : GrothendieckTopology C) (χ : p.Cleavage) {x y : S} (f g : x ⟶ y) :
    locallyEqual J χ f g ↔
      p.map f = p.map g ∧
        ∃ R : J.Cover (p.obj x), ∀ I : R.Arrow,
          χ.cartesianHom I.f (Functor.Fiber.mk (p := p) (a := x) rfl) ≫ f =
            χ.cartesianHom I.f (Functor.Fiber.mk (p := p) (a := x) rfl) ≫ g := sorry

/-- Local equality is independent of the selected cleavage.  The cleavage-explicit relation is
used to keep its construction concrete, while this theorem exposes its intrinsic meaning. -/
theorem locallyEqual_iff_of_cleavage
    (J : GrothendieckTopology C) (χ₁ χ₂ : p.Cleavage) {x y : S} (f g : x ⟶ y) :
    locallyEqual J χ₁ f g ↔ locallyEqual J χ₂ f g := sorry

/-- Local equality relative to a cleavage is reflexive. -/
theorem locallyEqual_refl (J : GrothendieckTopology C) (χ : p.Cleavage)
    {x y : S} (f : x ⟶ y) :
    locallyEqual J χ f f := sorry

/-- Local equality relative to a cleavage is symmetric. -/
theorem locallyEqual_symm (J : GrothendieckTopology C) (χ : p.Cleavage)
    {x y : S} {f g : x ⟶ y} (h : locallyEqual J χ f g) :
    locallyEqual J χ g f := sorry

/-- Local equality relative to a cleavage is transitive. -/
theorem locallyEqual_trans (J : GrothendieckTopology C) (χ : p.Cleavage)
    {x y : S} {f g h : x ⟶ y}
    (hfg : locallyEqual J χ f g) (hgh : locallyEqual J χ g h) :
    locallyEqual J χ f h := sorry

/-- Local equality is stable under postcomposition. -/
theorem locallyEqual_comp_right (J : GrothendieckTopology C) (χ : p.Cleavage)
    {x y z : S} {f g : x ⟶ y} (h : locallyEqual J χ f g) (a : y ⟶ z) :
    locallyEqual J χ (f ≫ a) (g ≫ a) := sorry

/-- Local equality is stable under precomposition. -/
theorem locallyEqual_comp_left (J : GrothendieckTopology C) (χ : p.Cleavage)
    {w x y : S} (a : w ⟶ x) {f g : x ⟶ y} (h : locallyEqual J χ f g) :
    locallyEqual J χ (a ≫ f) (a ≫ g) := sorry

/-- Local equality is stable under simultaneous pre- and postcomposition. -/
theorem locallyEqual_comp (J : GrothendieckTopology C) (χ : p.Cleavage)
    {w x y z : S} (a : w ⟶ x) {f g : x ⟶ y}
    (h : locallyEqual J χ f g) (b : y ⟶ z) :
    locallyEqual J χ ((a ≫ f) ≫ b) ((a ≫ g) ≫ b) := sorry

/-- Local equality can be cancelled after postcomposition with a strongly cartesian morphism
when the two candidate morphisms have the same base map. -/
theorem locallyEqual.of_comp_right_stronglyCartesian
    (J : GrothendieckTopology C) (χ : p.Cleavage)
    {U V : C} {q : U ⟶ V} {z x y : S} {φ : x ⟶ y}
    (hφ : p.IsStronglyCartesian q φ) {f g : z ⟶ x}
    (hbase : p.map f = p.map g)
    (hcomp : locallyEqual J χ (f ≫ φ) (g ≫ φ)) :
    locallyEqual J χ f g := sorry

/-- The Hom relation for the local-equality quotient category. -/
def homRel (J : GrothendieckTopology C) (χ : p.Cleavage) : HomRel S :=
  fun _ _ f g => locallyEqual J χ f g

/-- The local-equality Hom relation is exactly the local-equality predicate on each Hom set. -/
@[simp]
theorem homRel_iff (J : GrothendieckTopology C) (χ : p.Cleavage)
    {x y : S} (f g : x ⟶ y) :
    homRel J χ f g ↔ locallyEqual J χ f g := sorry

/-- The local-equality Hom relation is a congruence, so mathlib's quotient category identifies
exactly locally equal representatives rather than taking a larger compositional closure. -/
instance homRelCongruence (J : GrothendieckTopology C) (χ : p.Cleavage) :
    Congruence (homRel J χ) := sorry

/-- The category obtained by quotienting total-category morphisms by local equality.  This is
the canonical `CategoryTheory.Quotient` of `homRel`. -/
abbrev QuotientTotal (J : GrothendieckTopology C) (χ : p.Cleavage) :=
  CategoryTheory.Quotient (homRel J χ)

namespace QuotientTotal

/-- The object type of the local-equality quotient is canonically equivalent to the object type
of the original total category. The quotient changes morphisms, not objects. -/
def objectEquiv (J : GrothendieckTopology C) (χ : p.Cleavage) :
    QuotientTotal J χ ≃ S :=
  CategoryTheory.Quotient.equiv (homRel J χ)

/-- The quotient object represented by an original total-category object. -/
abbrev ofObj (J : GrothendieckTopology C) (χ : p.Cleavage) (x : S) : QuotientTotal J χ :=
  (CategoryTheory.Quotient.functor (homRel J χ)).obj x

/-- The local-equality class of a total-category morphism. -/
abbrev homMk (J : GrothendieckTopology C) (χ : p.Cleavage)
    {x y : S} (f : x ⟶ y) : ofObj J χ x ⟶ ofObj J χ y :=
  (CategoryTheory.Quotient.functor (homRel J χ)).map f

/-- Equality of local-equality quotient representatives is equivalent to local equality. -/
theorem homMk_eq_iff_locallyEqual (J : GrothendieckTopology C) (χ : p.Cleavage)
    {x y : S} {f g : x ⟶ y} :
    homMk J χ f = homMk J χ g ↔ locallyEqual J χ f g := sorry

/-- Equality of local-equality quotient representatives is equivalently equality of base maps
and coverage of the strict-equality restriction sieve. -/
theorem homMk_eq_iff_equalRestrictionSieve_mem
    (J : GrothendieckTopology C) (χ : p.Cleavage) {x y : S} {f g : x ⟶ y} :
    homMk J χ f = homMk J χ g ↔
      p.map f = p.map g ∧ equalRestrictionSieve χ f g ∈ J (p.obj x) := sorry

/-- A covering strict-equality restriction sieve identifies two local-equality quotient
representatives. -/
theorem homMk_eq_of_equalRestrictionSieve_mem
    (J : GrothendieckTopology C) (χ : p.Cleavage) {x y : S} {f g : x ⟶ y}
    (hbase : p.map f = p.map g)
    (hcover : equalRestrictionSieve χ f g ∈ J (p.obj x)) :
    homMk J χ f = homMk J χ g := sorry

/-- Quotient representatives agree when their cartesian restrictions agree over a covering
family. -/
theorem homMk_eq_of_cover_eq (J : GrothendieckTopology C) (χ : p.Cleavage)
    {x y : S} {f g : x ⟶ y}
    (hbase : p.map f = p.map g)
    (R : J.Cover (p.obj x))
    (hR : ∀ I : R.Arrow,
      homMk J χ
          (χ.cartesianHom I.f (Functor.Fiber.mk (p := p) (a := x) rfl) ≫ f) =
        homMk J χ
          (χ.cartesianHom I.f (Functor.Fiber.mk (p := p) (a := x) rfl) ≫ g)) :
    homMk J χ f = homMk J χ g := sorry

/-- Local equality follows when quotient representatives agree after cartesian restriction over
a covering family. -/
theorem locallyEqual_of_cover_eq (J : GrothendieckTopology C) (χ : p.Cleavage)
    {x y : S} {f g : x ⟶ y}
    (hbase : p.map f = p.map g)
    (R : J.Cover (p.obj x))
    (hR : ∀ I : R.Arrow,
      homMk J χ
          (χ.cartesianHom I.f (Functor.Fiber.mk (p := p) (a := x) rfl) ≫ f) =
        homMk J χ
          (χ.cartesianHom I.f (Functor.Fiber.mk (p := p) (a := x) rfl) ≫ g)) :
    locallyEqual J χ f g := sorry

/-- The canonical projection from the local-equality quotient category to the base category. -/
def projection (J : GrothendieckTopology C) (χ : p.Cleavage) : QuotientTotal J χ ⥤ C :=
  CategoryTheory.Quotient.lift (homRel J χ) p (fun _ _ _ _ h ↦ h.1)

/-- The quotient projection has the original projection on underlying objects. -/
@[simp]
theorem projection_obj (J : GrothendieckTopology C) (χ : p.Cleavage)
    (x : QuotientTotal J χ) :
    (projection J χ).obj x = p.obj x.as := sorry

/-- The quotient projection sends a representative to its original base map. -/
@[simp]
theorem projection_map_homMk (J : GrothendieckTopology C) (χ : p.Cleavage)
    {x y : S} (f : x ⟶ y) :
    (projection J χ).map (homMk J χ f) = p.map f := sorry

/-- A strongly cartesian representative remains strongly cartesian after passing to its
local-equality class. -/
theorem homMk_isStronglyCartesian (J : GrothendieckTopology C) (χ : p.Cleavage)
    {U V : C} {q : U ⟶ V} {x y : S} (φ : x ⟶ y)
    (hφ : p.IsStronglyCartesian q φ) :
    (projection J χ).IsStronglyCartesian q (homMk J χ φ) := sorry

/-- Quotient morphisms are equal when their base maps agree and their precomposites by the
chosen cartesian arrows of a cover are equal. -/
theorem eq_of_cover_comp_homMk_eq (J : GrothendieckTopology C) (χ : p.Cleavage) {x y : S}
    (a b : ofObj J χ x ⟶ ofObj J χ y)
    (hbase : (projection J χ).map a = (projection J χ).map b)
    (R : J.Cover (p.obj x))
    (hR : ∀ I : R.Arrow,
      homMk J χ
          (χ.cartesianHom I.f (Functor.Fiber.mk (p := p) (a := x) rfl)) ≫ a =
        homMk J χ
          (χ.cartesianHom I.f (Functor.Fiber.mk (p := p) (a := x) rfl)) ≫ b) :
    a = b := sorry

/-- Quotient morphisms are equal when they agree after precomposition by any strongly cartesian
testing family over a cover. -/
theorem eq_of_cover_comp_stronglyCartesian
    (J : GrothendieckTopology C) (χ : p.Cleavage) {x y : S}
    (a b : ofObj J χ x ⟶ ofObj J χ y)
    (hbase : (projection J χ).map a = (projection J χ).map b)
    (R : J.Cover (p.obj x))
    (w : R.Arrow → QuotientTotal J χ)
    (φ : ∀ I : R.Arrow, w I ⟶ ofObj J χ x)
    (hφ : ∀ I : R.Arrow, (projection J χ).IsStronglyCartesian I.f (φ I))
    (hR : ∀ I : R.Arrow, φ I ≫ a = φ I ≫ b) :
    a = b := sorry

/-- Fiber morphisms of the quotient projection are equal when a covering strongly cartesian
testing family makes their underlying composites equal. -/
theorem fiberHom.eq_of_cover_comp_stronglyCartesian
    (J : GrothendieckTopology C) (χ : p.Cleavage) {U : C}
    {x y : (projection J χ).Fiber U} (a b : x ⟶ y)
    (R : J.Cover U)
    (w : R.Arrow → QuotientTotal J χ)
    (φ : ∀ I : R.Arrow, w I ⟶ x.1)
    (hφ : ∀ I : R.Arrow, (projection J χ).IsStronglyCartesian I.f (φ I))
    (hR : ∀ I : R.Arrow, φ I ≫ a.1 = φ I ≫ b.1) :
    a = b := sorry

/-- The local-equality quotient projection is fibred over the base category. -/
instance projectionIsFibered (J : GrothendieckTopology C) (χ : p.Cleavage) :
    (projection J χ).IsFibered := sorry

/-- The canonical quotient functor from the original total category. -/
abbrev quotientFunctor (J : GrothendieckTopology C) (χ : p.Cleavage) :
    S ⥤ QuotientTotal J χ :=
  CategoryTheory.Quotient.functor (homRel J χ)

/-- The local-equality quotient functor commutes with the projection to the base. -/
theorem quotientFunctor_comp_projection (J : GrothendieckTopology C) (χ : p.Cleavage) :
    quotientFunctor J χ ⋙ projection J χ = p := sorry

end QuotientTotal

end LocalEquality

end Functor.Cleavage

end CategoryTheory
