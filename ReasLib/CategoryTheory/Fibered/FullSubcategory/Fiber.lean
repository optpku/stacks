/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibers of full subcategories

For an object property `P : ObjectProperty X` and a functor `p : X ⥤ C`, the fiber of the
restricted projection `P.ι ⋙ p` over `U` is canonically equivalent to the full subcategory of the
ambient fiber `p.Fiber U` on objects satisfying `P`.

The data constructions use mathlib's `Functor.Fiber.inducedFunctor` and `ObjectProperty.lift`.
This module owns the resulting fiber comparison; applications should import it directly rather
than reproduce the two factorization transports.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty.Fiber

open Functor
open Functor.Fiber

variable {C : Type u₁} {X : Type u₂} [Category.{v₁} C] [Category.{v₂} X]

/-- The inclusion of a full subcategory, regarded canonically as a based functor from the
restricted projection `P.ι ⋙ p` to the ambient projection `p`. -/
def inclusion (P : ObjectProperty X) (p : X ⥤ C) :
    BasedCategory.ofFunctor (P.ι ⋙ p) ⥤ᵇ BasedCategory.ofFunctor p where
  toFunctor := P.ι

/-- The canonical forgetful functor from the fiber of `P.ι ⋙ p` to the ambient fiber. -/
noncomputable def forget (P : ObjectProperty X) (p : X ⥤ C) (U : C) :
    (P.ι ⋙ p).Fiber U ⥤ p.Fiber U :=
  (inclusion P p).fiberFunctor U

/-- Forgetting a restricted-fiber object preserves its underlying total-category object. -/
@[simp]
theorem forget.obj_val (P : ObjectProperty X) (p : X ⥤ C) (U : C)
    (x : (P.ι ⋙ p).Fiber U) :
    ((forget P p U).obj x).1 = x.1.obj := sorry

/-- Forgetting a restricted-fiber morphism preserves its underlying total-category morphism. -/
@[simp]
theorem forget.map_val (P : ObjectProperty X) (p : X ⥤ C) (U : C)
    {x y : (P.ι ⋙ p).Fiber U} (f : x ⟶ y) :
    ((forget P p U).map f).1 = f.1.hom := sorry

/-- Every object obtained by forgetting from the restricted fiber satisfies the inverse-image
property in the ambient fiber. -/
theorem forget.property (P : ObjectProperty X) (p : X ⥤ C) (U : C)
    (x : (P.ι ⋙ p).Fiber U) :
    (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X))
      ((forget P p U).obj x) := sorry

/-- Objects in the inverse-image full subcategory of the ambient fiber satisfy `P` after
forgetting to the total category. -/
theorem liftTotal.property (P : ObjectProperty X) (p : X ⥤ C) (U : C)
    (x : (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory) :
    P x.obj.1 := sorry

/-- The full subcategory of the ambient fiber cut out by `P` maps to the total full subcategory. -/
noncomputable def liftTotal (P : ObjectProperty X) (p : X ⥤ C)
    (U : C) :
    (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory ⥤ P.FullSubcategory :=
  P.lift
    ((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).ι ⋙
      (fiberInclusion : p.Fiber U ⥤ X))
    (liftTotal.property P p U)

/-- The total-category object of the lift from the ambient-fiber full subcategory. -/
@[simp]
theorem liftTotal.obj (P : ObjectProperty X) (p : X ⥤ C) (U : C)
    (x : (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory) :
    ((liftTotal P p U).obj x).obj = x.obj.1 := sorry

/-- The total-category morphism of the lift from the ambient-fiber full subcategory. -/
@[simp]
theorem liftTotal.map (P : ObjectProperty X) (p : X ⥤ C) (U : C)
    {x y : (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory}
    (f : x ⟶ y) :
    ((liftTotal P p U).map f).hom = f.hom.1 := sorry

/-- The total full-subcategory functor induced by an inverse-image fiber is constant over `U`. -/
theorem liftTotal.comp (P : ObjectProperty X) (p : X ⥤ C)
    (U : C) :
    liftTotal P p U ⋙ (P.ι ⋙ p) =
      (const ((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory)).obj U := sorry

/-- The canonical functor from the inverse-image full subcategory of the ambient fiber back to
the fiber of the restricted projection. -/
noncomputable def fromFullSubcategory (P : ObjectProperty X) (p : X ⥤ C) (U : C) :
    (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory ⥤ (P.ι ⋙ p).Fiber U :=
  Functor.Fiber.inducedFunctor
    (liftTotal.comp P p U)

/-- The total full-subcategory object underlying `fromFullSubcategory`. -/
@[simp]
theorem fromFullSubcategory.obj_val (P : ObjectProperty X) (p : X ⥤ C) (U : C)
    (x : (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory) :
    ((fromFullSubcategory P p U).obj x).1 = (liftTotal P p U).obj x := sorry

/-- The total full-subcategory morphism underlying `fromFullSubcategory`. -/
@[simp]
theorem fromFullSubcategory.map_val (P : ObjectProperty X) (p : X ⥤ C) (U : C)
    {x y : (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory}
    (f : x ⟶ y) :
    ((fromFullSubcategory P p U).map f).1 = (liftTotal P p U).map f := sorry

/-- The canonical functor from the restricted fiber to the full subcategory of the ambient fiber
cut out by `P`. -/
noncomputable def toFullSubcategory (P : ObjectProperty X) (p : X ⥤ C) (U : C) :
    (P.ι ⋙ p).Fiber U ⥤
      (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory :=
  (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).lift
    (forget P p U)
    (forget.property P p U)

/-- The ambient-fiber object underlying `toFullSubcategory`. -/
@[simp]
theorem toFullSubcategory.obj (P : ObjectProperty X) (p : X ⥤ C) (U : C)
    (x : (P.ι ⋙ p).Fiber U) :
    ((toFullSubcategory P p U).obj x).obj = (forget P p U).obj x := sorry

/-- The ambient-fiber morphism underlying `toFullSubcategory`. -/
@[simp]
theorem toFullSubcategory.map (P : ObjectProperty X) (p : X ⥤ C) (U : C)
    {x y : (P.ι ⋙ p).Fiber U} (f : x ⟶ y) :
    ((toFullSubcategory P p U).map f).hom = (forget P p U).map f := sorry

/-! ## Explicit unit and counit -/

/-- The identity on the underlying selected object is vertical for the restricted projection.
This is the proof field used by `unitApp`; it does not determine the ambient isomorphism. -/
theorem unitApp.isHomLift
    (P : ObjectProperty X) (p : X ⥤ C) (U : C)
    (x : (P.ι ⋙ p).Fiber U) :
    (P.ι ⋙ p).IsHomLift (𝟙 U)
      (ObjectProperty.homMk (𝟙 x.1.obj) :
        x.1 ⟶ ((toFullSubcategory P p U ⋙ fromFullSubcategory P p U).obj x).1) := sorry

/-- The objectwise unit of the full-subcategory fiber comparison. Its ambient non-`Prop` datum is
the identity isomorphism of the original selected total-category object. -/
noncomputable def unitApp
    (P : ObjectProperty X) (p : X ⥤ C) (U : C)
    (x : (P.ι ⋙ p).Fiber U) :
    x ≅ (toFullSubcategory P p U ⋙ fromFullSubcategory P p U).obj x :=
  Functor.Fiber.isoMk (ObjectProperty.isoMk P (Iso.refl x.1.obj))
    (unitApp.isHomLift P p U x)

/-- The explicit unit components are natural in restricted-fiber morphisms. -/
theorem unitApp.naturality
    (P : ObjectProperty X) (p : X ⥤ C) (U : C)
    {x y : (P.ι ⋙ p).Fiber U} (f : x ⟶ y) :
    f ≫ (unitApp P p U y).hom =
      (unitApp P p U x).hom ≫
        (toFullSubcategory P p U ⋙ fromFullSubcategory P p U).map f := sorry

/-- The explicit comparison from the identity on the restricted fiber to the
forward-then-inverse fiber comparison. -/
noncomputable def unitIso
    (P : ObjectProperty X) (p : X ⥤ C) (U : C) :
    𝟭 ((P.ι ⋙ p).Fiber U) ≅
      toFullSubcategory P p U ⋙ fromFullSubcategory P p U :=
  NatIso.ofComponents (unitApp P p U)
    (fun f ↦ unitApp.naturality P p U f)

/-- The identity on the underlying ambient-fiber object is vertical for `p`. This proof is the
only non-data input used to construct `counitApp`. -/
theorem counitApp.isHomLift
    (P : ObjectProperty X) (p : X ⥤ C) (U : C)
    (x : (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory) :
    p.IsHomLift (𝟙 U) (𝟙 x.obj.1) := sorry

/-- The objectwise counit of the full-subcategory fiber comparison. Its ambient non-`Prop` datum
is the identity isomorphism of the original object in `p.Fiber U`. -/
noncomputable def counitApp
    (P : ObjectProperty X) (p : X ⥤ C) (U : C)
    (x : (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory) :
    (fromFullSubcategory P p U ⋙ toFullSubcategory P p U).obj x ≅ x :=
  ObjectProperty.isoMk (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X))
    (Functor.Fiber.isoMk (Iso.refl x.obj.1) (counitApp.isHomLift P p U x))

/-- The explicit counit components are natural in morphisms of the inverse-image full
subcategory. -/
theorem counitApp.naturality
    (P : ObjectProperty X) (p : X ⥤ C) (U : C)
    {x y : (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory}
    (f : x ⟶ y) :
    (fromFullSubcategory P p U ⋙ toFullSubcategory P p U).map f ≫
        (counitApp P p U y).hom =
      (counitApp P p U x).hom ≫ f := sorry

/-- The explicit comparison from the inverse-then-forward fiber comparison to the identity on
the inverse-image full subcategory. -/
noncomputable def counitIso
    (P : ObjectProperty X) (p : X ⥤ C) (U : C) :
    fromFullSubcategory P p U ⋙ toFullSubcategory P p U ≅
      𝟭 ((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory) :=
  NatIso.ofComponents (counitApp P p U)
    (fun f ↦ counitApp.naturality P p U f)

/-- The canonical equivalence between the fiber of the full subcategory and the corresponding
full subcategory of the ambient fiber. -/
@[stacks 04TU "fiber of a full subcategory"]
noncomputable def equivalence (P : ObjectProperty X) (p : X ⥤ C) (U : C) :
    (P.ι ⋙ p).Fiber U ≌
      (P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).FullSubcategory :=
  CategoryTheory.Equivalence.mk
    (toFullSubcategory P p U)
    (fromFullSubcategory P p U)
    (unitIso P p U)
    (counitIso P p U)

/-- The forward functor of the fiber equivalence is `toFullSubcategory`. -/
@[simp]
theorem equivalence.functor (P : ObjectProperty X) (p : X ⥤ C) (U : C) :
    (equivalence P p U).functor = toFullSubcategory P p U := sorry

/-- The inverse functor of the fiber equivalence is `fromFullSubcategory`. -/
@[simp]
theorem equivalence.inverse (P : ObjectProperty X) (p : X ⥤ C) (U : C) :
    (equivalence P p U).inverse = fromFullSubcategory P p U := sorry

/-- The unit of the fiber equivalence is the explicit identity-owner unit. -/
@[simp]
theorem equivalence.unitIso (P : ObjectProperty X) (p : X ⥤ C) (U : C) :
    (equivalence P p U).unitIso = unitIso P p U := sorry

/-- The counit of the fiber equivalence is the explicit identity-owner counit. -/
@[simp]
theorem equivalence.counitIso (P : ObjectProperty X) (p : X ⥤ C) (U : C) :
    (equivalence P p U).counitIso = counitIso P p U := sorry

end CategoryTheory.ObjectProperty.Fiber

/- Data audit: `unitApp` and `counitApp` are assembled from explicit identity isomorphisms by
`Functor.Fiber.isoMk` and `ObjectProperty.isoMk`. Deferred axioms occur only in verticality,
naturality, and inverse-law proofs; no functor or isomorphism is selected from a proposition. -/
