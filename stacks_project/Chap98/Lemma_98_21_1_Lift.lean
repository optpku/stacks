/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Groupoid
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Fibers

/-!
# Fibered categories of lifts along a base morphism

For a functor `p : 𝒳 ⥤ 𝒮`, a base morphism `f : U ⟶ V`, and a fibre object `x`
over `U`, the category `p.UnderLift f x` has as objects the morphisms `x ⟶ x'`
lying over `f`, and as morphisms the fibre morphisms over `V` making the
under-triangle commute.
-/

@[expose] public section

universe v₁ u₁ v₂ u₂

open CategoryTheory

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- The category of lifts of a fibre object `x` along a base morphism `f`. Objects are
arrows out of `x` lying over `f`. -/
def UnderLift (p : 𝒳 ⥤ 𝒮) {U V : 𝒮} (f : U ⟶ V) (x : p.Fiber U) : Type max u₂ v₂ :=
  { a : Under (Fiber.fiberInclusion.obj x) // p.IsHomLift f a.hom }

namespace UnderLift

variable {p : 𝒳 ⥤ 𝒮} {U V : 𝒮} {f : U ⟶ V} {x : p.Fiber U}

/-- A lift is a total morphism lying over the given base arrow. -/
instance isHomLift (a : UnderLift p f x) : p.IsHomLift f a.val.hom := a.property

/-- The codomain object in the total category of a lift. -/
abbrev right (a : UnderLift p f x) : 𝒳 := a.val.right

/-- The underlying total morphism of a lift. -/
abbrev hom (a : UnderLift p f x) : Fiber.fiberInclusion.obj x ⟶ a.right := a.val.hom

/-- The codomain of a lift, as an object of the fibre over the codomain of `f`. -/
def codomain (a : UnderLift p f x) : p.Fiber V :=
  Fiber.mk (IsHomLift.codomain_eq p f a.hom)

end UnderLift

variable {p : 𝒳 ⥤ 𝒮} {U V : 𝒮} {f : U ⟶ V} {x : p.Fiber U}

/-- Morphisms of lifts are morphisms in the fibre over the codomain of `f` that fill the
under-triangle. -/
instance underLiftCategory : Category.{v₂} (UnderLift p f x) where
  Hom a b :=
    { η : UnderLift.codomain a ⟶ UnderLift.codomain b //
      a.val.hom ≫ Fiber.fiberInclusion.map η = b.val.hom }
  id a := ⟨𝟙 (UnderLift.codomain a), sorry⟩
  comp η θ := ⟨η.val ≫ θ.val, sorry⟩
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

namespace UnderLift

variable {p : 𝒳 ⥤ 𝒮} {U V : 𝒮} {f : U ⟶ V} {x : p.Fiber U}

/-- Package a total morphism lying over `f` as an object of the lift category. -/
def ofHom (f : U ⟶ V) (x : p.Fiber U) {y : 𝒳}
    (φ : Fiber.fiberInclusion.obj x ⟶ y) [h : p.IsHomLift f φ] :
    UnderLift p f x :=
  ⟨Under.mk φ, Under.mk_hom φ ▸ h⟩

/-- The packaged lift recovers the supplied total morphism. -/
theorem ofHom_hom (f : U ⟶ V) (x : p.Fiber U) {y : 𝒳}
    (φ : Fiber.fiberInclusion.obj x ⟶ y) [p.IsHomLift f φ] :
    (ofHom f x φ).hom = φ := sorry

/-- The fibre-codomain of a packaged lift is the target of the supplied morphism. -/
theorem ofHom_right (f : U ⟶ V) (x : p.Fiber U) {y : 𝒳}
    (φ : Fiber.fiberInclusion.obj x ⟶ y) [p.IsHomLift f φ] :
    (ofHom f x φ).right = y := sorry

/-- Build a morphism of lifts from a fibre morphism filling the under-triangle. -/
def homMk {a b : UnderLift p f x} (η : a.codomain ⟶ b.codomain)
    (w : a.hom ≫ Fiber.fiberInclusion.map η = b.hom) : a ⟶ b :=
  ⟨η, w⟩

/-- `homMk` recovers the supplied fibre morphism. -/
theorem homMk_val {a b : UnderLift p f x} (η : a.codomain ⟶ b.codomain)
    (w : a.hom ≫ Fiber.fiberInclusion.map η = b.hom) :
    (homMk η w).val = η := sorry

/-- The forgetful functor from the lift category to the total category. -/
def forget : UnderLift p f x ⥤ 𝒳 where
  obj a := a.right
  map η := Fiber.fiberInclusion.map η.val
  map_id := sorry
  map_comp := sorry

/-- The forgetful functor sends a lift to the codomain of its underlying arrow. -/
theorem forget_obj (a : UnderLift p f x) : forget.obj a = a.right := sorry

/-- The forgetful functor sends a morphism of lifts to the underlying total morphism. -/
theorem forget_map {a b : UnderLift p f x} (η : a ⟶ b) :
    forget.map η = Fiber.fiberInclusion.map η.val := sorry

/-- A lift is a total morphism lying over `f` whose codomain lies over the codomain of `f`. -/
theorem spec (a : UnderLift p f x) :
    p.IsHomLift f a.hom ∧ p.obj a.right = V := sorry

/-- A morphism of lifts is a fibre morphism over `𝟙 V` filling the under-triangle. -/
theorem hom_spec {a b : UnderLift p f x} (η : a ⟶ b) :
    p.IsHomLift (𝟙 V) (Fiber.fiberInclusion.map η.val) ∧
      a.hom ≫ Fiber.fiberInclusion.map η.val = b.hom := sorry

/-- The fibre-codomain of a lift is the codomain object of its underlying arrow. -/
theorem codomain_obj (a : UnderLift p f x) :
    Fiber.fiberInclusion.obj a.codomain = a.right := sorry

end UnderLift

/-- If `p` is fibred in groupoids, then the category of lifts along `f` is a groupoid. -/
instance underLiftIsGroupoid [IsFibered.InGroupoids p] :
    IsGroupoid (UnderLift p f x) := sorry

end CategoryTheory.Functor
