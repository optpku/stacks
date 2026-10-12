/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Groupoid
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Fibers

/-!
# Categories of lifts along a base morphism

For a functor `p : 𝒳 ⥤ 𝒮`, a base morphism `f : R ⟶ S`, and an object `x` of the
fibre `p.Fiber S`, the category `p.ObjectLift f x` has as objects the morphisms
`x' ⟶ x` lying over `f`, and as morphisms the fibre morphisms over `R` making the
over-triangle commute. The type `p.lifts f x` records isomorphism classes of this
category.
-/

@[expose] public section

universe v₁ u₁ v₂ u₂

open CategoryTheory

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- The category of lifts of a fibre object `x` along a base morphism `f`. Objects are
arrows to `x` lying over `f`. -/
def ObjectLift (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} (f : R ⟶ S) (x : p.Fiber S) : Type max u₂ v₂ :=
  { a : Over (Fiber.fiberInclusion.obj x) // p.IsHomLift f a.hom }

namespace ObjectLift

variable {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {f : R ⟶ S} {x : p.Fiber S}

/-- A lift is a total morphism lying over the given base arrow. -/
instance isHomLift (a : ObjectLift p f x) : p.IsHomLift f a.val.hom := a.property

/-- The domain object in the total category of a lift. -/
abbrev left (a : ObjectLift p f x) : 𝒳 := a.val.left

/-- The underlying total morphism of a lift. -/
abbrev hom (a : ObjectLift p f x) : a.left ⟶ Fiber.fiberInclusion.obj x := a.val.hom

/-- The domain of a lift, as an object of the fibre over the domain of `f`. -/
def domain (a : ObjectLift p f x) : p.Fiber R :=
  Fiber.mk (IsHomLift.domain_eq p f a.hom)

end ObjectLift

variable {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {f : R ⟶ S} {x : p.Fiber S}

/-- Morphisms of lifts are morphisms in the fibre over the domain of `f` that fill the
over-triangle. -/
instance objectLiftCategory : Category.{v₂} (ObjectLift p f x) where
  Hom a b :=
    { η : ObjectLift.domain a ⟶ ObjectLift.domain b //
      Fiber.fiberInclusion.map η ≫ b.val.hom = a.val.hom }
  id a := ⟨𝟙 (ObjectLift.domain a), sorry⟩
  comp η θ := ⟨η.val ≫ θ.val, sorry⟩
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

namespace ObjectLift

variable {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {f : R ⟶ S} {x : p.Fiber S}

/-- Package a total morphism lying over `f` as an object of the lift category. -/
def ofHom (f : R ⟶ S) (x : p.Fiber S) {y : 𝒳}
    (φ : y ⟶ Fiber.fiberInclusion.obj x) [h : p.IsHomLift f φ] :
    ObjectLift p f x :=
  ⟨Over.mk φ, Over.mk_hom φ ▸ h⟩

/-- The packaged lift recovers the supplied total morphism. -/
theorem ofHom_hom (f : R ⟶ S) (x : p.Fiber S) {y : 𝒳}
    (φ : y ⟶ Fiber.fiberInclusion.obj x) [p.IsHomLift f φ] :
    (ofHom f x φ).hom = φ := sorry

/-- The fibre-domain of a packaged lift is the source of the supplied morphism. -/
theorem ofHom_left (f : R ⟶ S) (x : p.Fiber S) {y : 𝒳}
    (φ : y ⟶ Fiber.fiberInclusion.obj x) [p.IsHomLift f φ] :
    (ofHom f x φ).left = y := sorry

/-- Build a morphism of lifts from a fibre morphism filling the over-triangle. -/
def homMk {a b : ObjectLift p f x} (η : a.domain ⟶ b.domain)
    (w : Fiber.fiberInclusion.map η ≫ b.hom = a.hom) : a ⟶ b :=
  ⟨η, w⟩

/-- `homMk` recovers the supplied fibre morphism. -/
theorem homMk_val {a b : ObjectLift p f x} (η : a.domain ⟶ b.domain)
    (w : Fiber.fiberInclusion.map η ≫ b.hom = a.hom) :
    (homMk η w).val = η := sorry

/-- The forgetful functor from the lift category to the total category. -/
def forget : ObjectLift p f x ⥤ 𝒳 where
  obj a := a.left
  map η := Fiber.fiberInclusion.map η.val
  map_id := sorry
  map_comp := sorry

/-- The forgetful functor sends a lift to the domain of its underlying arrow. -/
theorem forget_obj (a : ObjectLift p f x) : forget.obj a = a.left := sorry

/-- The forgetful functor sends a morphism of lifts to the underlying total morphism. -/
theorem forget_map {a b : ObjectLift p f x} (η : a ⟶ b) :
    forget.map η = Fiber.fiberInclusion.map η.val := sorry

/-- A lift is a total morphism lying over `f` whose domain lies over the domain of `f`. -/
theorem spec (a : ObjectLift p f x) :
    p.IsHomLift f a.hom ∧ p.obj a.left = R := sorry

/-- A morphism of lifts is a fibre morphism over `𝟙 R` filling the over-triangle. -/
theorem hom_spec {a b : ObjectLift p f x} (η : a ⟶ b) :
    p.IsHomLift (𝟙 R) (Fiber.fiberInclusion.map η.val) ∧
      Fiber.fiberInclusion.map η.val ≫ b.hom = a.hom := sorry

/-- The fibre-domain of a lift is the domain object of its underlying arrow. -/
theorem domain_obj (a : ObjectLift p f x) :
    Fiber.fiberInclusion.obj a.domain = a.left := sorry

end ObjectLift

/-- If `p` is cofibered in groupoids, then the category of lifts along `f` is a groupoid. -/
instance objectLiftIsGroupoid [IsFibered.InGroupoids p.op] :
    IsGroupoid (ObjectLift p f x) := sorry

/-- The type of isomorphism classes of lifts of `x` along `f`. -/
def lifts (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} (f : R ⟶ S) (x : p.Fiber S) : Type max u₂ v₂ :=
  isomorphismClasses.obj (Cat.of (ObjectLift p f x))

/-- The isomorphism class of a lift is the class of the packaged underlying morphism. -/
theorem lifts_mk (a : ObjectLift p f x) :
    (Quotient.mk'' a : lifts p f x) = Quotient.mk'' (ObjectLift.ofHom f x a.hom) := sorry

end CategoryTheory.Functor
