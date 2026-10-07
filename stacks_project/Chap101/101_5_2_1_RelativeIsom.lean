module

public import Mathlib.CategoryTheory.Subfunctor.Equalizer
public import stacks_project.Chap101.«101_3_3_1_Isom»

/-!
# Relative automorphism sheaf as a kernel of `isomMap`

For a morphism of groupoid fibrations, `Isom_{X/Y}(x, x)` is the kernel of
`Isom_X(x, x) ⟶ Isom_Y(f(x), f(x))` at the identity section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

/-- Identity section of `Isom_Y(f(x), f(x))` over the identity slice of `T`. -/
def identitySection (f : X ⟶ Y) {T : Over S} (x : X.p.Fiber T) :
    (isom ((fiberFunctor f T).obj x) ((fiberFunctor f T).obj x)).obj
      (op (Over.mk (𝟙 T))) :=
  (alphaSection f x x (Iso.refl _)).app (op (Over.mk (𝟙 T)))
    (ULift.up (𝟙 (Over.mk (𝟙 T))))

/-- The constant identity comparison `Isom_X(x, x) ⟶ Isom_Y(f(x), f(x))`. -/
def constIdentity (f : X ⟶ Y) {T : Over S} (x : X.p.Fiber T) :
    isom x x ⟶
      isom ((fiberFunctor f T).obj x) ((fiberFunctor f T).obj x) where
  app W :=
    TypeCat.ofHom fun _ ↦
      (isom ((fiberFunctor f T).obj x) ((fiberFunctor f T).obj x)).map
        (Over.homMk (unop W).hom (Category.comp_id (unop W).hom)).op
        (identitySection f x)
  naturality := sorry

/-- The kernel sheaf `Isom_{X/Y}(x, x)` of `isomMap` at the identity. -/
def relativeIsom (f : X ⟶ Y) {T : Over S} (x : X.p.Fiber T) :
    (Over T)ᵒᵖ ⥤ Type (u + 1) :=
  (Subfunctor.equalizer
      ((⊤ : Subfunctor (isom x x)).ι ≫ isomMap f x x)
      ((⊤ : Subfunctor (isom x x)).ι ≫ constIdentity f x)).toFunctor

/-- Canonical inclusion `Isom_{X/Y}(x, x) ⟶ Isom_X(x, x)`. -/
def relativeIsom.ι (f : X ⟶ Y) {T : Over S} (x : X.p.Fiber T) :
    relativeIsom f x ⟶ isom x x :=
  (Subfunctor.equalizer
      ((⊤ : Subfunctor (isom x x)).ι ≫ isomMap f x x)
      ((⊤ : Subfunctor (isom x x)).ι ≫ constIdentity f x)).ι

/-- The inclusion equalizes `isomMap` and the identity section. -/
theorem relativeIsom.condition (f : X ⟶ Y) {T : Over S} (x : X.p.Fiber T) :
    relativeIsom.ι f x ≫ isomMap f x x =
      relativeIsom.ι f x ≫ constIdentity f x :=
  sorry

/-- Pointwise membership in `relativeIsom` is the kernel condition for `isomMap`. -/
theorem mem_relativeIsom_iff (f : X ⟶ Y) {T : Over S} (x : X.p.Fiber T)
    {T' : Over T} (φ : (isom x x).obj (op T')) :
    (∃ ψ : (relativeIsom f x).obj (op T'),
        (relativeIsom.ι f x).app (op T') ψ = φ) ↔
      (isomMap f x x).app (op T') φ =
        (constIdentity f x).app (op T') φ :=
  sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal
