module

public import ReasLib.CategoryTheory.Semigroupal.Basic
public import Mathlib.CategoryTheory.Equivalence

@[expose] public section

universe v u

namespace CategoryTheory.SemigroupalCategory

variable {C : Type u} [Category.{v} C]

section

variable [SemigroupalCategory C]

/-- A unit for a coherent tensor is an object with natural left and right unitors
satisfying the triangle identity. -/
structure Unit (C : Type u) [Category.{v} C] [SemigroupalCategory C] where
  /-- The unit object. -/
  obj : C
  /-- The natural left unitor. -/
  leftUnitor : tensorLeft obj ≅ 𝟭 C
  /-- The natural right unitor. -/
  rightUnitor : tensorRight obj ≅ 𝟭 C
  /-- The triangle identity for the associator and the two unitors. -/
  triangle :
    ∀ X Y : C,
      (associator X obj Y).hom ≫ whiskerLeft X (leftUnitor.hom.app Y) =
        whiskerRight (rightUnitor.hom.app X) Y

/-- A cancellable idempotent is an object with a multiplication isomorphism such that
tensoring on either side by that object is an equivalence. -/
structure UnitSeed (C : Type u) [Category.{v} C] [SemigroupalCategory C] where
  /-- The cancellable idempotent object. -/
  obj : C
  /-- The multiplication isomorphism. -/
  mul : tensorObj obj obj ≅ obj
  /-- Left tensoring by the object is an equivalence. -/
  tensorLeft_isEquivalence : (tensorLeft obj).IsEquivalence
  /-- Right tensoring by the object is an equivalence. -/
  tensorRight_isEquivalence : (tensorRight obj).IsEquivalence

/-- The unitors of a unit satisfy the triangle identity. -/
theorem Unit.spec (unit : Unit C) :
    ∀ X Y : C,
      (associator X unit.obj Y).hom ≫ whiskerLeft X (unit.leftUnitor.hom.app Y) =
        whiskerRight (unit.rightUnitor.hom.app X) Y := unit.triangle

/-- Constructing a unit preserves its object, unitors, and triangle identity. -/
theorem Unit.mk_spec (unitObj : C) (left : tensorLeft unitObj ≅ 𝟭 C)
    (right : tensorRight unitObj ≅ 𝟭 C)
    (triangleLaw : ∀ X Y : C,
      (associator X unitObj Y).hom ≫ whiskerLeft X (left.hom.app Y) =
        whiskerRight (right.hom.app X) Y) :
    (Unit.mk unitObj left right triangleLaw).obj = unitObj ∧
    (Unit.mk unitObj left right triangleLaw).leftUnitor = left ∧
    (Unit.mk unitObj left right triangleLaw).rightUnitor = right ∧
    ∀ X Y : C,
      (associator X unitObj Y).hom ≫ whiskerLeft X (left.hom.app Y) =
        whiskerRight (right.hom.app X) Y := ⟨rfl, rfl, rfl, triangleLaw⟩

/-- Tensoring on either side by a cancellable idempotent is an equivalence. -/
theorem UnitSeed.spec (seed : UnitSeed C) :
    (tensorLeft seed.obj).IsEquivalence ∧ (tensorRight seed.obj).IsEquivalence :=
  ⟨seed.tensorLeft_isEquivalence, seed.tensorRight_isEquivalence⟩

/-- Constructing a cancellable idempotent preserves its object, multiplication,
and both equivalence properties. -/
theorem UnitSeed.mk_spec (unitObj : C) (mul : tensorObj unitObj unitObj ≅ unitObj)
    (leftEquivalence : (tensorLeft unitObj).IsEquivalence)
    (rightEquivalence : (tensorRight unitObj).IsEquivalence) :
    (UnitSeed.mk unitObj mul leftEquivalence rightEquivalence).obj = unitObj ∧
    (UnitSeed.mk unitObj mul leftEquivalence rightEquivalence).mul = mul ∧
    (tensorLeft unitObj).IsEquivalence ∧ (tensorRight unitObj).IsEquivalence :=
  ⟨rfl, rfl, leftEquivalence, rightEquivalence⟩

/-- The triangle identity expressed using the inverse associator. -/
theorem triangle_stacks (unit : Unit C) (X Y : C) :
    (associator X unit.obj Y).inv ≫ whiskerRight (unit.rightUnitor.hom.app X) Y =
      whiskerLeft X (unit.leftUnitor.hom.app Y) := sorry

/-- An explicit equivalence property supplies fully faithful morphism preimages. -/
private noncomputable def fullyFaithfulOf (functor : C ⥤ C)
    (equivalence : functor.IsEquivalence) : functor.FullyFaithful :=
  @Functor.FullyFaithful.ofFullyFaithful _ _ _ _ functor equivalence.full equivalence.faithful

/-- The left unitor component recovered by fully faithful left tensoring. -/
@[no_expose] noncomputable def UnitSeed.leftUnitorIso (seed : UnitSeed C) (X : C) :
    tensorObj seed.obj X ≅ X := by
  exact (fullyFaithfulOf (tensorLeft seed.obj) seed.tensorLeft_isEquivalence).preimageIso
    ((associator seed.obj seed.obj X).symm ≪≫ whiskerRightIso seed.mul X)

/-- The right unitor component recovered by fully faithful right tensoring. -/
@[no_expose] noncomputable def UnitSeed.rightUnitorIso (seed : UnitSeed C) (X : C) :
    tensorObj X seed.obj ≅ X := by
  exact (fullyFaithfulOf (tensorRight seed.obj) seed.tensorRight_isEquivalence).preimageIso
    (associator X seed.obj seed.obj ≪≫ whiskerLeftIso X seed.mul)

/-- The reconstructed left unitor components are natural in the object. -/
theorem UnitSeed.leftUnitor_naturality (seed : UnitSeed C) {X Y : C} (morphism : X ⟶ Y) :
    (tensorLeft seed.obj).map morphism ≫ (seed.leftUnitorIso Y).hom =
      (seed.leftUnitorIso X).hom ≫ morphism := sorry

/-- The reconstructed right unitor components are natural in the object. -/
theorem UnitSeed.rightUnitor_naturality (seed : UnitSeed C) {X Y : C} (morphism : X ⟶ Y) :
    (tensorRight seed.obj).map morphism ≫ (seed.rightUnitorIso Y).hom =
      (seed.rightUnitorIso X).hom ≫ morphism := sorry

/-- The natural left unitor recovered from a cancellable idempotent. -/
noncomputable def UnitSeed.leftUnitor (seed : UnitSeed C) : tensorLeft seed.obj ≅ 𝟭 C :=
  NatIso.ofComponents seed.leftUnitorIso seed.leftUnitor_naturality

/-- The natural right unitor recovered from a cancellable idempotent. -/
noncomputable def UnitSeed.rightUnitor (seed : UnitSeed C) : tensorRight seed.obj ≅ 𝟭 C :=
  NatIso.ofComponents seed.rightUnitorIso seed.rightUnitor_naturality

/-- Left tensoring the recovered left unitor gives the inverse associator
followed by multiplication tensored on the right. -/
theorem leftUnitor_char (seed : UnitSeed C) (X : C) :
    (tensorLeft seed.obj).mapIso (seed.leftUnitor.app X) =
      (associator seed.obj seed.obj X).symm ≪≫ whiskerRightIso seed.mul X := sorry

/-- Right tensoring the recovered right unitor gives the associator
followed by multiplication tensored on the left. -/
theorem rightUnitor_char (seed : UnitSeed C) (X : C) :
    (tensorRight seed.obj).mapIso (seed.rightUnitor.app X) =
      associator X seed.obj seed.obj ≪≫ whiskerLeftIso X seed.mul := sorry

/-- A unit gives a cancellable idempotent whose multiplication is its right unitor
evaluated at the unit object. -/
def UnitSeed.ofUnit (unit : Unit C) : UnitSeed C where
  obj := unit.obj
  mul := unit.rightUnitor.app unit.obj
  tensorLeft_isEquivalence := Functor.isEquivalence_of_iso unit.leftUnitor.symm
  tensorRight_isEquivalence := Functor.isEquivalence_of_iso unit.rightUnitor.symm

/-- Passing from a unit to a cancellable idempotent preserves the object. -/
theorem UnitSeed.ofUnit_obj (unit : Unit C) : (UnitSeed.ofUnit unit).obj = unit.obj := rfl

/-- The reconstructed left and right unitors satisfy the triangle identity. -/
theorem Unit.ofSeed_triangle (seed : UnitSeed C) (X Y : C) :
    (associator X seed.obj Y).hom ≫ whiskerLeft X (seed.leftUnitor.hom.app Y) =
      whiskerRight (seed.rightUnitor.hom.app X) Y := sorry

/-- A cancellable idempotent gives a unit with the reconstructed natural unitors. -/
noncomputable def Unit.ofSeed (seed : UnitSeed C) : Unit C where
  obj := seed.obj
  leftUnitor := seed.leftUnitor
  rightUnitor := seed.rightUnitor
  triangle := Unit.ofSeed_triangle seed

/-- Reconstructing a unit from a cancellable idempotent preserves the object. -/
theorem Unit.ofSeed_obj (seed : UnitSeed C) : (Unit.ofSeed seed).obj = seed.obj := rfl

/-- Reconstructing the unit associated to a unit's cancellable idempotent recovers that unit. -/
theorem Unit.ofSeed_ofUnit (unit : Unit C) : Unit.ofSeed (UnitSeed.ofUnit unit) = unit := sorry

/-- Taking the cancellable idempotent of a reconstructed unit recovers its object
and specified multiplication. -/
theorem UnitSeed.ofUnit_ofSeed (seed : UnitSeed C) : UnitSeed.ofUnit (Unit.ofSeed seed) = seed :=
  sorry

/-- Units correspond bijectively to cancellable idempotents with specified multiplication. -/
noncomputable def unitEquiv (C : Type u) [Category.{v} C] [SemigroupalCategory C] :
    Unit C ≃ UnitSeed C where
  toFun := UnitSeed.ofUnit
  invFun := Unit.ofSeed
  left_inv := Unit.ofSeed_ofUnit
  right_inv := UnitSeed.ofUnit_ofSeed

/-- The forward correspondence takes a unit to its cancellable idempotent. -/
theorem unitEquiv_apply (unit : Unit C) : unitEquiv C unit = UnitSeed.ofUnit unit := rfl

/-- The inverse correspondence reconstructs a unit from a cancellable idempotent. -/
theorem unitEquiv_symm_apply (seed : UnitSeed C) :
    (unitEquiv C).symm seed = Unit.ofSeed seed := rfl

/-- The correspondence preserves the object in the forward direction. -/
theorem unitEquiv_obj (unit : Unit C) : (unitEquiv C unit).obj = unit.obj := rfl

/-- The correspondence preserves the object in the inverse direction. -/
theorem unitEquiv_symm_obj (seed : UnitSeed C) : ((unitEquiv C).symm seed).obj = seed.obj := rfl

end

section ofMonoidal

variable [MonoidalCategory C]

open MonoidalCategory

/-- The supplied monoidal unit and unitors give a unit for the underlying coherent tensor. -/
noncomputable def Unit.ofMonoidal : Unit C where
  obj := 𝟙_ C
  leftUnitor := NatIso.ofComponents (fun X ↦ λ_ X) (fun morphism ↦ by
    simpa only [tensorLeft, Functor.curryObj, CategoryTheory.SemigroupalCategory.tensor,
      instSemigroupalCategory,
      CategoryTheory.SemigroupalCategory.ofMonoidal, MonoidalCategory.tensor,
      MonoidalCategory.id_tensorHom, Functor.id_map, Functor.id_obj] using
      MonoidalCategory.leftUnitor_naturality morphism)
  rightUnitor := NatIso.ofComponents (fun X ↦ ρ_ X) (fun morphism ↦ by
    simpa only [tensorRight, Functor.flip, Functor.curryObj, CategoryTheory.SemigroupalCategory.tensor,
      instSemigroupalCategory,
      CategoryTheory.SemigroupalCategory.ofMonoidal, MonoidalCategory.tensor,
      MonoidalCategory.tensorHom_id, Functor.id_map, Functor.id_obj] using
      MonoidalCategory.rightUnitor_naturality morphism)
  triangle X Y := by
    simpa only [whiskerLeft, whiskerRight, tensorObj, tensorLeft, tensorRight,
      Functor.curryObj, Functor.flip, Functor.id_obj,
      associator, CategoryTheory.SemigroupalCategory.tensor, instSemigroupalCategory,
      CategoryTheory.SemigroupalCategory.ofMonoidal, MonoidalCategory.tensor,
      MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id,
      NatIso.ofComponents_hom_app] using
      MonoidalCategory.triangle X Y

/-- The unit obtained from a monoidal category has its given monoidal unit object. -/
theorem Unit.ofMonoidal_obj : (Unit.ofMonoidal : Unit C).obj = 𝟙_ C := rfl

/-- The supplied monoidal unit yields a cancellable idempotent via its right unitor. -/
noncomputable def UnitSeed.ofMonoidal : UnitSeed C :=
  UnitSeed.ofUnit Unit.ofMonoidal

/-- The cancellable idempotent obtained from a monoidal category has its monoidal unit object. -/
theorem UnitSeed.ofMonoidal_obj : (UnitSeed.ofMonoidal : UnitSeed C).obj = 𝟙_ C := rfl

end ofMonoidal

end CategoryTheory.SemigroupalCategory
