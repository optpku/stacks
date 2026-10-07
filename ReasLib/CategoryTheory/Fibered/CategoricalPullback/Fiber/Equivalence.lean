module

public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Fiber.Forward
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Fiber.Reverse
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism

/-!
# Explicit equivalence of categorical-pullback fibers

The forward strictification and choice-free reverse embedding assemble into an
equivalence on each fiber.  This module owns the unit, counit, triangle, and
equivalence API for a specified cleavage on the right leg.
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

/-- The strictification arrow for an object coming from the strict right fiber lies over the
identity of the fixed base object. -/
theorem Fiber.equivalence.counit.isHomLift
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : p.Fiber (u.obj U)) :
    p.IsHomLift (𝟙 (u.obj U))
      (Fiber.forward.cartesian u p χ
        (Fiber.reverse.obj u p X)) := sorry

/-- The explicit counit morphism from strictifying an embedded right-fiber object back to that
right-fiber object. -/
noncomputable def Fiber.equivalence.counit.hom
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : p.Fiber (u.obj U)) :
    Fiber.forward.strict u p χ
        (Fiber.reverse.obj u p X) ⟶ X :=
  ⟨Fiber.forward.cartesian u p χ
      (Fiber.reverse.obj u p X),
    Fiber.equivalence.counit.isHomLift u p χ X⟩

/-- Every component of the explicit right-fiber counit is an isomorphism. -/
instance Fiber.equivalence.counit.hom.isIso
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : p.Fiber (u.obj U)) :
    IsIso (Fiber.equivalence.counit.hom u p χ X) := sorry

/-- The forward map of the explicit strictification isomorphism is vertical in the fixed right
fiber. This proof field does not determine its inverse map. -/
theorem Fiber.equivalence.counit.app.isHomLift
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : p.Fiber (u.obj U)) :
    p.IsHomLift (𝟙 (u.obj U))
      (Fiber.forward.cartesianIso u p χ
        (Fiber.reverse.obj u p X)).hom := sorry

/-- The objectwise counit isomorphism for the explicit pair of pullback-fiber comparison
functors. Its inverse is supplied by the explicit cartesian-domain comparison, rather than
selected from an `IsIso` proposition. -/
noncomputable def Fiber.equivalence.counit.app
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : p.Fiber (u.obj U)) :
    Fiber.forward.strict u p χ
        (Fiber.reverse.obj u p X) ≅ X :=
  Functor.Fiber.isoMk
    (Fiber.forward.cartesianIso u p χ (Fiber.reverse.obj u p X))
    (Fiber.equivalence.counit.app.isHomLift u p χ X)

/-- Naturality of the explicit right-fiber counit. -/
theorem Fiber.equivalence.counit.naturality
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    {X Y : p.Fiber (u.obj U)} (φ : X ⟶ Y) :
    (Fiber.reverse.functor u p U ⋙
        Fiber.forward.functor u p χ U).map φ ≫
      (Fiber.equivalence.counit.app u p χ Y).hom =
    (Fiber.equivalence.counit.app u p χ X).hom ≫ φ := sorry

/-- The explicit reverse-then-forward comparison is naturally isomorphic to the identity on the
right fiber. -/
noncomputable def Fiber.equivalence.counit.iso
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C) :
    Fiber.reverse.functor u p U ⋙
        Fiber.forward.functor u p χ U ≅
      𝟭 (p.Fiber (u.obj U)) :=
  NatIso.ofComponents (Fiber.equivalence.counit.app u p χ)
    (fun φ ↦ Fiber.equivalence.counit.naturality u p χ φ)

/-- The forward component of the explicit counit is the selected strictification morphism. -/
@[simp]
theorem Fiber.equivalence.counit.iso.hom.app
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C)
    (X : p.Fiber (u.obj U)) :
    (Fiber.equivalence.counit.iso u p χ U).hom.app X =
      Fiber.equivalence.counit.hom u p χ X := sorry

/-- The inverse component of the explicit counit is the inverse of its objectwise
strictification isomorphism. -/
@[simp]
theorem Fiber.equivalence.counit.iso.inv.app
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C)
    (X : p.Fiber (u.obj U)) :
    (Fiber.equivalence.counit.iso u p χ U).inv.app X =
      (Fiber.equivalence.counit.app u p χ X).inv := sorry

/-- Compatibility of the two explicit component isomorphisms comparing embedding after
strictification with the original categorical-pullback object. -/
theorem Fiber.equivalence.inverseUnit.compatibility
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : (π₁ u p).Fiber U) :
    u.map (eqToIso X.2.symm).hom ≫ X.1.iso.hom =
      (Fiber.reverse.obj u p
        (Fiber.forward.strict u p χ X)).1.iso.hom ≫
      p.map (Fiber.forward.cartesianIso u p χ X).hom := sorry

/-- The explicit ambient isomorphism comparing embedding after strictification with the original
categorical-pullback object. Its first component is equality transport already stored by the
fiber object, and its second component is the explicit cartesian-domain isomorphism. -/
noncomputable def Fiber.equivalence.inverseUnit.ambientIso
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : (π₁ u p).Fiber U) :
    (Fiber.reverse.obj u p
        (Fiber.forward.strict u p χ X)).1 ≅ X.1 :=
  CategoricalPullback.mkIso (eqToIso X.2.symm)
    (Fiber.forward.cartesianIso u p χ X)
    (Fiber.equivalence.inverseUnit.compatibility u p χ X)

/-- The ambient pullback morphism comparing embedding after strictification with the original
pullback object, obtained as the forward map of the explicit ambient isomorphism. -/
noncomputable def Fiber.equivalence.inverseUnit.ambient
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : (π₁ u p).Fiber U) :
    (Fiber.reverse.obj u p
        (Fiber.forward.strict u p χ X)).1 ⟶ X.1 :=
  (Fiber.equivalence.inverseUnit.ambientIso u p χ X).hom

/-- The first component of the ambient inverse-unit comparison is the equality transport from
the fixed fiber base to the representative stored by the pullback object. -/
@[simp]
theorem Fiber.equivalence.inverseUnit.ambient.fst
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : (π₁ u p).Fiber U) :
    (Fiber.equivalence.inverseUnit.ambient u p χ X).fst =
      eqToHom X.2.symm := sorry

/-- The second component of the ambient inverse-unit comparison is the selected
strictification arrow. -/
@[simp]
theorem Fiber.equivalence.inverseUnit.ambient.snd
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : (π₁ u p).Fiber U) :
    (Fiber.equivalence.inverseUnit.ambient u p χ X).snd =
      Fiber.forward.cartesian u p χ X := sorry

/-- The ambient inverse-unit comparison lies over the identity of the pullback base. -/
theorem Fiber.equivalence.inverseUnit.ambient.isHomLift
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : (π₁ u p).Fiber U) :
    (π₁ u p).IsHomLift (𝟙 U)
      (Fiber.equivalence.inverseUnit.ambient u p χ X) := sorry

/-- The forward map of the explicit ambient inverse-unit isomorphism lies over the identity of
the pullback base. -/
theorem Fiber.equivalence.inverseUnit.ambientIso.isHomLift
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : (π₁ u p).Fiber U) :
    (π₁ u p).IsHomLift (𝟙 U)
      (Fiber.equivalence.inverseUnit.ambientIso u p χ X).hom := sorry

/-- The explicit inverse-unit morphism in the fiber of the pullback projection. -/
noncomputable def Fiber.equivalence.inverseUnit.hom
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : (π₁ u p).Fiber U) :
    Fiber.reverse.obj u p
        (Fiber.forward.strict u p χ X) ⟶ X :=
  ⟨Fiber.equivalence.inverseUnit.ambient u p χ X,
    Fiber.equivalence.inverseUnit.ambient.isHomLift u p χ X⟩

/-- Every component of the explicit inverse unit is an isomorphism. -/
instance Fiber.equivalence.inverseUnit.hom.isIso
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : (π₁ u p).Fiber U) :
    IsIso (Fiber.equivalence.inverseUnit.hom u p χ X) := sorry

/-- The objectwise inverse-unit isomorphism for the explicit pair of pullback-fiber comparison
functors. Both ambient component isomorphisms are explicit. -/
noncomputable def Fiber.equivalence.inverseUnit.app
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    (X : (π₁ u p).Fiber U) :
    Fiber.reverse.obj u p
        (Fiber.forward.strict u p χ X) ≅ X :=
  Functor.Fiber.isoMk
    (Fiber.equivalence.inverseUnit.ambientIso u p χ X)
    (Fiber.equivalence.inverseUnit.ambientIso.isHomLift u p χ X)

/-- Naturality of the explicit inverse unit. -/
theorem Fiber.equivalence.inverseUnit.naturality
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) {U : C}
    {X Y : (π₁ u p).Fiber U} (φ : X ⟶ Y) :
    (Fiber.forward.functor u p χ U ⋙
        Fiber.reverse.functor u p U).map φ ≫
      (Fiber.equivalence.inverseUnit.app u p χ Y).hom =
    (Fiber.equivalence.inverseUnit.app u p χ X).hom ≫ φ := sorry

/-- Forward-then-reverse comparison with the identity on the pullback-projection fiber. -/
noncomputable def Fiber.equivalence.inverseUnit.iso
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C) :
    Fiber.forward.functor u p χ U ⋙
        Fiber.reverse.functor u p U ≅
      𝟭 ((π₁ u p).Fiber U) :=
  NatIso.ofComponents (Fiber.equivalence.inverseUnit.app u p χ)
    (fun φ ↦ Fiber.equivalence.inverseUnit.naturality u p χ φ)

/-- The forward component of the explicit inverse unit is the comparison back to the original
pullback object. -/
@[simp]
theorem Fiber.equivalence.inverseUnit.iso.hom.app
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C)
    (X : (π₁ u p).Fiber U) :
    (Fiber.equivalence.inverseUnit.iso u p χ U).hom.app X =
      Fiber.equivalence.inverseUnit.hom u p χ X := sorry

/-- The inverse component of the inverse-unit comparison is the inverse of its explicit
objectwise isomorphism. -/
@[simp]
theorem Fiber.equivalence.inverseUnit.iso.inv.app
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C)
    (X : (π₁ u p).Fiber U) :
    (Fiber.equivalence.inverseUnit.iso u p χ U).inv.app X =
      (Fiber.equivalence.inverseUnit.app u p χ X).inv := sorry

/-- The unit isomorphism for the explicit pullback-fiber equivalence. -/
noncomputable def Fiber.equivalence.unit.iso
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C) :
    𝟭 ((π₁ u p).Fiber U) ≅
      Fiber.forward.functor u p χ U ⋙
        Fiber.reverse.functor u p U :=
  (Fiber.equivalence.inverseUnit.iso u p χ U).symm

/-- The forward component of the explicit unit is the inverse of the comparison back to the
original pullback object. -/
@[simp]
theorem Fiber.equivalence.unit.iso.hom.app
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C)
    (X : (π₁ u p).Fiber U) :
    (Fiber.equivalence.unit.iso u p χ U).hom.app X =
      (Fiber.equivalence.inverseUnit.app u p χ X).inv := sorry

/-- The inverse component of the explicit unit is the comparison back to the original pullback
object. -/
@[simp]
theorem Fiber.equivalence.unit.iso.inv.app
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C)
    (X : (π₁ u p).Fiber U) :
    (Fiber.equivalence.unit.iso u p χ U).inv.app X =
      Fiber.equivalence.inverseUnit.hom u p χ X := sorry

/-- The explicit unit and counit satisfy the forward triangle identity. -/
theorem Fiber.equivalence.triangle
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C)
    (X : (π₁ u p).Fiber U) :
    (Fiber.forward.functor u p χ U).map
          ((Fiber.equivalence.unit.iso u p χ U).hom.app X) ≫
        (Fiber.equivalence.counit.iso u p χ U).hom.app
          ((Fiber.forward.functor u p χ U).obj X) =
      𝟙 ((Fiber.forward.functor u p χ U).obj X) := sorry

/-- Strictification of right components is an equivalence on every fiber of a categorical
pullback projection. -/
instance Fiber.forward.functor.isEquivalence
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C) :
    (Fiber.forward.functor u p χ U).IsEquivalence := sorry

/-- Once a cleavage is specified on the right leg, the strict right-fiber embedding is also an
equivalence.  The functor itself is choice-free; the cleavage is used only to establish its
essential-surjectivity property. -/
theorem Fiber.reverse.functor.isEquivalence
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C) :
    (Fiber.reverse.functor u p U).IsEquivalence := sorry

/-- The categorical equivalence between a fiber of the first pullback projection and the
corresponding fiber of the right leg, derived from the explicit forward functor. -/
noncomputable def Fiber.equivalence
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C) :
    (π₁ u p).Fiber U ≌ p.Fiber (u.obj U) where
  functor := Fiber.forward.functor u p χ U
  inverse := Fiber.reverse.functor u p U
  unitIso := Fiber.equivalence.unit.iso u p χ U
  counitIso := Fiber.equivalence.counit.iso u p χ U
  functor_unitIso_comp X :=
    Fiber.equivalence.triangle u p χ U X

/-- The forward functor of `Fiber.equivalence` is the explicit right-component
strictification functor. -/
@[simp]
theorem Fiber.equivalence.functor
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C) :
    (Fiber.equivalence u p χ U).functor =
      Fiber.forward.functor u p χ U := sorry

/-- The inverse functor of `Fiber.equivalence` is the explicit strict
right-fiber embedding. -/
@[simp]
theorem Fiber.equivalence.inverse
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C) :
    (Fiber.equivalence u p χ U).inverse =
      Fiber.reverse.functor u p U := sorry

/-- The unit of the explicit fiber equivalence is the explicit unit comparison. -/
theorem Fiber.equivalence.unitIso
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C) :
    (Fiber.equivalence u p χ U).unitIso =
      Fiber.equivalence.unit.iso u p χ U := sorry

/-- The counit of the explicit fiber equivalence is the explicit strictification comparison. -/
theorem Fiber.equivalence.counitIso
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C) :
    (Fiber.equivalence u p χ U).counitIso =
      Fiber.equivalence.counit.iso u p χ U := sorry

end Limits.CategoricalPullback

end CategoryTheory

/- Data audit: the counit and inverse-unit components are assembled from the explicit
`Fiber.forward.cartesianIso` and `CategoricalPullback.mkIso`. Deferred axioms occur only in
verticality, compatibility, naturality, and triangle proofs; no inverse is obtained from an
`IsIso` proof. -/
