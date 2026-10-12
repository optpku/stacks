/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Cleavage
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Comparison

/-!
# Forward comparison of categorical-pullback fibers

For an explicit cleavage on the right leg, this module strictifies the right
component of a fiber of the first categorical-pullback projection.  It owns the
object, arrow, and functor computations for that choice-explicit comparison.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

universe uC uD uS vC vD vS

namespace CategoryTheory

open Functor

namespace Limits.CategoricalPullback

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- The structural isomorphism from the strict base point `u.obj U` to the right component of an
object in the fiber of `π₁ u p` over `U`. -/
noncomputable def Fiber.forward.iso
    (u : C ⥤ D) (p : S ⥤ D) {U : C}
    (X : (π₁ u p).Fiber U) :
    u.obj U ≅ p.obj X.1.snd :=
  eqToIso (congrArg u.obj X.2).symm ≪≫ X.1.iso

/-- The right component of a categorical-pullback object, regarded as an object of the fiber over
its actual image under `p`. -/
def Fiber.forward.obj
    (u : C ⥤ D) (p : S ⥤ D) {U : C}
    (X : (π₁ u p).Fiber U) :
    p.Fiber (p.obj X.1.snd) :=
  ⟨X.1.snd, rfl⟩

/-- Strictify the right component of a fiber object using a specified cleavage on `p`. -/
noncomputable def Fiber.forward.strict
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : (π₁ u p).Fiber U) :
    p.Fiber (u.obj U) :=
  χ.reindexObj (Fiber.forward.iso u p X).hom
    (Fiber.forward.obj u p X)

/-- The selected cartesian arrow from the strictified right component back to the original right
component. -/
noncomputable def Fiber.forward.cartesian
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : (π₁ u p).Fiber U) :
    (Fiber.forward.strict u p χ X).1 ⟶ X.1.snd :=
  χ.cartesianHom (Fiber.forward.iso u p X).hom
    (Fiber.forward.obj u p X)

/-- The selected strictification arrow over the structural base isomorphism, promoted to an
explicit isomorphism by the canonical comparison with the identity cartesian arrow. -/
noncomputable def Fiber.forward.cartesianIso
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : (π₁ u p).Fiber U) :
    (Fiber.forward.strict u p χ X).1 ≅ X.1.snd :=
  Functor.IsStronglyCartesian.DomainIso.ofBaseIso
    (g := Fiber.forward.iso u p X) p
    (Category.comp_id (Fiber.forward.iso u p X).hom).symm
    (𝟙 X.1.snd) (Fiber.forward.cartesian u p χ X)
    (inferInstance :
      p.IsStronglyCartesian (𝟙 (p.obj X.1.snd)) (𝟙 X.1.snd))
    (χ.reindexLift (Fiber.forward.iso u p X).hom
      (Fiber.forward.obj u p X)).isStronglyCartesian

/-- The forward map of `cartesianIso` is the selected strictification arrow. -/
@[simp]
theorem Fiber.forward.cartesianIso.hom
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : (π₁ u p).Fiber U) :
    (Fiber.forward.cartesianIso u p χ X).hom =
      Fiber.forward.cartesian u p χ X := sorry

/-- The forward structural map of `Fiber.forward.iso`. -/
@[simp]
theorem Fiber.forward.iso.hom
    (u : C ⥤ D) (p : S ⥤ D) {U : C}
    (X : (π₁ u p).Fiber U) :
    (Fiber.forward.iso u p X).hom =
      eqToHom (congrArg u.obj X.2).symm ≫ X.1.iso.hom := sorry

/-- The inverse structural map of `Fiber.forward.iso`. -/
@[simp]
theorem Fiber.forward.iso.inv
    (u : C ⥤ D) (p : S ⥤ D) {U : C}
    (X : (π₁ u p).Fiber U) :
    (Fiber.forward.iso u p X).inv =
      X.1.iso.inv ≫ eqToHom (congrArg u.obj X.2) := sorry

/-- The selected strictification arrow is strongly cartesian over the structural right-base
isomorphism. -/
instance Fiber.forward.cartesian.stronglyCartesian
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : (π₁ u p).Fiber U) :
    p.IsStronglyCartesian (Fiber.forward.iso u p X).hom
      (Fiber.forward.cartesian u p χ X) := sorry

/-- The selected strictification arrow is an isomorphism: it is strongly cartesian over the
structural base isomorphism. -/
instance Fiber.forward.cartesian.isIso
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : (π₁ u p).Fiber U) :
    IsIso (Fiber.forward.cartesian u p χ X) := sorry

/-- The structural right-base isomorphism is natural with respect to vertical morphisms in the
fiber of the first projection. -/
@[reassoc]
theorem Fiber.forward.iso.hom.naturality
    (u : C ⥤ D) (p : S ⥤ D) {U : C}
    {X Y : (π₁ u p).Fiber U} (φ : X ⟶ Y) :
    (Fiber.forward.iso u p X).hom ≫ p.map φ.1.snd =
      (Fiber.forward.iso u p Y).hom := sorry

/-- The composite to the right component of `Y` has the base map required to factor through the
selected strictification arrow of `Y`. -/
instance Fiber.forward.map.isHomLift
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    {X Y : (π₁ u p).Fiber U} (φ : X ⟶ Y) :
    p.IsHomLift
      (𝟙 (u.obj U) ≫ (Fiber.forward.iso u p Y).hom)
      (Fiber.forward.cartesian u p χ X ≫ φ.1.snd) := sorry

/-- The morphism between strictified right components forced by cartesian factorization. -/
noncomputable def Fiber.forward.map
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    {X Y : (π₁ u p).Fiber U} (φ : X ⟶ Y) :
    Fiber.forward.strict u p χ X ⟶
      Fiber.forward.strict u p χ Y :=
  ⟨(@Functor.Cleavage.cartesianFactor D _ S _ p χ
      (p.obj Y.1.snd) (u.obj U) (u.obj U)
      (Fiber.forward.iso u p Y).hom
      (𝟙 (u.obj U)) (Fiber.forward.obj u p Y)
      (Fiber.forward.strict u p χ X).1
      (Fiber.forward.cartesian u p χ X ≫ φ.1.snd)
      (Fiber.forward.map.isHomLift u p χ φ)),
    (@Functor.Cleavage.cartesianFactor.isHomLift D _ S _ p χ
      (p.obj Y.1.snd) (u.obj U) (u.obj U)
      (Fiber.forward.iso u p Y).hom
      (𝟙 (u.obj U)) (Fiber.forward.obj u p Y)
      (Fiber.forward.strict u p χ X).1
      (Fiber.forward.cartesian u p χ X ≫ φ.1.snd)
      (Fiber.forward.map.isHomLift u p χ φ))⟩

/-- The strictified right-component map is characterized by its composite with the selected
cartesian strictification arrow. -/
@[reassoc]
theorem Fiber.forward.map.fac
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    {X Y : (π₁ u p).Fiber U} (φ : X ⟶ Y) :
    (Fiber.forward.map u p χ φ).1 ≫
        Fiber.forward.cartesian u p χ Y =
      Fiber.forward.cartesian u p χ X ≫ φ.1.snd := sorry

/-- Strictification of right components preserves identity morphisms. -/
theorem Fiber.forward.map.id
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : (π₁ u p).Fiber U) :
    Fiber.forward.map u p χ (𝟙 X) =
      𝟙 (Fiber.forward.strict u p χ X) := sorry

/-- Strictification of right components preserves composition. -/
theorem Fiber.forward.map.comp
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    {X Y Z : (π₁ u p).Fiber U} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    Fiber.forward.map u p χ (φ ≫ ψ) =
      Fiber.forward.map u p χ φ ≫
        Fiber.forward.map u p χ ψ := sorry

/-- The canonical functor from a fiber of the first categorical-pullback projection to the
corresponding fiber of its right leg. -/
noncomputable def Fiber.forward.functor
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C) :
    (π₁ u p).Fiber U ⥤ p.Fiber (u.obj U) where
  obj X := Fiber.forward.strict u p χ X
  map φ := Fiber.forward.map u p χ φ
  map_id X := Fiber.forward.map.id u p χ X
  map_comp φ ψ := Fiber.forward.map.comp u p χ φ ψ

/-- Objectwise computation for `Fiber.forward.functor`. -/
@[simp]
theorem Fiber.forward.functor.obj
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C)
    (X : (π₁ u p).Fiber U) :
    (Fiber.forward.functor u p χ U).obj X =
      Fiber.forward.strict u p χ X := sorry

/-- Morphismwise computation for `Fiber.forward.functor`. -/
@[simp]
theorem Fiber.forward.functor.map
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C)
    {X Y : (π₁ u p).Fiber U} (φ : X ⟶ Y) :
    (Fiber.forward.functor u p χ U).map φ =
      Fiber.forward.map u p χ φ := sorry

end Limits.CategoricalPullback

end CategoryTheory
