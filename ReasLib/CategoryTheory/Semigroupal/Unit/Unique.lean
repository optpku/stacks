module

public import ReasLib.CategoryTheory.Semigroupal.Unit
public import Mathlib.Algebra.Group.Defs
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Logic.Unique

@[expose] public section

universe v u

namespace CategoryTheory.SemigroupalCategory

variable {C : Type u} [Category.{v} C] [SemigroupalCategory C]

/-- The two whiskerings of a cancellable idempotent's multiplication agree
after inserting the associator. -/
theorem UnitSeed.mul_whisker_eq (seed : UnitSeed C) :
    whiskerRight seed.mul.hom seed.obj =
      (associator seed.obj seed.obj seed.obj).hom ≫ whiskerLeft seed.obj seed.mul.hom := sorry

/-- Endomorphisms of a cancellable idempotent form a commutative monoid
with the usual categorical composition multiplication. -/
def UnitSeed.endCommMonoid (seed : UnitSeed C) : CommMonoid (End seed.obj) where
  toMonoid := End.monoid
  mul_comm := sorry

/-- Every endomorphism of a cancellable idempotent is recovered by conjugating
its right whiskering by the multiplication. -/
theorem UnitSeed.conj_whiskerRight (seed : UnitSeed C) (endomorphism : seed.obj ⟶ seed.obj) :
    endomorphism = seed.mul.inv ≫ whiskerRight endomorphism seed.obj ≫ seed.mul.hom := sorry

/-- Every endomorphism of a cancellable idempotent is recovered by conjugating
its left whiskering by the multiplication. -/
theorem UnitSeed.conj_whiskerLeft (seed : UnitSeed C) (endomorphism : seed.obj ⟶ seed.obj) :
    endomorphism = seed.mul.inv ≫ whiskerLeft seed.obj endomorphism ≫ seed.mul.hom := sorry

/-- Every endomorphism of a cancellable idempotent equals both multiplication
conjugates of its whiskerings. -/
theorem UnitSeed.conj (seed : UnitSeed C) (endomorphism : seed.obj ⟶ seed.obj) :
    endomorphism = seed.mul.inv ≫ whiskerRight endomorphism seed.obj ≫ seed.mul.hom ∧
      endomorphism = seed.mul.inv ≫ whiskerLeft seed.obj endomorphism ≫ seed.mul.hom :=
  ⟨seed.conj_whiskerRight endomorphism, seed.conj_whiskerLeft endomorphism⟩

/-- A multiplication-preserving isomorphism between two cancellable idempotents. -/
structure UnitSeedIso (first second : UnitSeed C) where
  /-- The isomorphism between the supplied objects. -/
  iso : first.obj ≅ second.obj
  /-- The isomorphism intertwines the two specified multiplications. -/
  map_mul :
    tensorHom iso.hom iso.hom ≫ second.mul.hom = first.mul.hom ≫ iso.hom

/-- The underlying isomorphism of a unit-seed isomorphism preserves multiplication. -/
theorem UnitSeedIso.spec {first second : UnitSeed C} (comparison : UnitSeedIso first second) :
    tensorHom comparison.iso.hom comparison.iso.hom ≫ second.mul.hom =
      first.mul.hom ≫ comparison.iso.hom := comparison.map_mul

/-- Constructing a unit-seed isomorphism preserves its isomorphism and multiplication square. -/
theorem UnitSeedIso.mk_spec {first second : UnitSeed C} (comparison : first.obj ≅ second.obj)
    (compatibility : tensorHom comparison.hom comparison.hom ≫ second.mul.hom =
      first.mul.hom ≫ comparison.hom) :
    (UnitSeedIso.mk comparison compatibility).iso = comparison ∧
      tensorHom comparison.hom comparison.hom ≫ second.mul.hom =
        first.mul.hom ≫ comparison.hom := ⟨rfl, compatibility⟩

/-- A unit-seed isomorphism is determined by its underlying object isomorphism. -/
theorem UnitSeedIso.ext {first second : UnitSeed C}
    {comparison other : UnitSeedIso first second} (equality : comparison.iso = other.iso) :
    comparison = other := sorry

namespace UnitSeedIso

/-- The reconstructed unitors give the unique multiplication-preserving
isomorphism between two cancellable idempotents. -/
noncomputable def unique (first second : UnitSeed C) : UnitSeedIso first second where
  iso := (second.rightUnitor.app first.obj).symm ≪≫ first.leftUnitor.app second.obj
  map_mul := sorry

/-- The canonical comparison is the inverse right unitor followed by the left unitor. -/
theorem unique_iso (first second : UnitSeed C) :
    (unique first second).iso =
      (second.rightUnitor.app first.obj).symm ≪≫ first.leftUnitor.app second.obj := rfl

/-- Every multiplication-preserving comparison equals the canonical unitor comparison. -/
theorem eq_unique {first second : UnitSeed C} (comparison : UnitSeedIso first second) :
    comparison = unique first second := sorry

end UnitSeedIso

/-- A cancellable idempotent has associator-compatible multiplication, commutative
endomorphism composition, both whiskering conjugation identities, and a unique
multiplication-preserving isomorphism from every other cancellable idempotent. -/
theorem UnitSeed.unit_unique (seed : UnitSeed C) :
    (whiskerRight seed.mul.hom seed.obj =
      (associator seed.obj seed.obj seed.obj).hom ≫ whiskerLeft seed.obj seed.mul.hom) ∧
    (∀ first second : End seed.obj, first * second = second * first) ∧
    (∀ endomorphism : seed.obj ⟶ seed.obj,
      endomorphism = seed.mul.inv ≫ whiskerRight endomorphism seed.obj ≫ seed.mul.hom ∧
      endomorphism = seed.mul.inv ≫ whiskerLeft seed.obj endomorphism ≫ seed.mul.hom) ∧
    (∀ second : UnitSeed C, ∃! comparison : second.obj ≅ seed.obj,
      tensorHom comparison.hom comparison.hom ≫ seed.mul.hom =
        second.mul.hom ≫ comparison.hom) := by
  refine ⟨seed.mul_whisker_eq, (seed.endCommMonoid).mul_comm, seed.conj, ?_⟩
  intro second
  refine ⟨(UnitSeedIso.unique second seed).iso, (UnitSeedIso.unique second seed).map_mul, ?_⟩
  intro comparison compatibility
  exact congrArg UnitSeedIso.iso (UnitSeedIso.eq_unique (UnitSeedIso.mk comparison compatibility))

end CategoryTheory.SemigroupalCategory
