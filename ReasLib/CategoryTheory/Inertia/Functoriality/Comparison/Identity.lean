module

public import ReasLib.CategoryTheory.Inertia.Functoriality.Comparison.IdentityComposition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity comparison for inertia functoriality

This leaf owns the explicit identity comparison of the raw inertia action and its componentwise
computation and naturality API.
-/

@[expose] public section

open CategoryTheory

universe uC vC

namespace CategoryTheory
namespace Inertia

variable {C : Type uC} [Category.{vC} C]

namespace mapIdIso

/-- The identity underlying arrow intertwines the automorphism obtained by mapping with the
identity functor and the original automorphism. -/
theorem app.comm (X : Inertia C) :
    ((map (𝟭 C)).obj X).aut.hom ≫ 𝟙 X.obj =
      𝟙 X.obj ≫ X.aut.hom := sorry

/-- The objectwise identity comparison for inertia. Its underlying ambient isomorphism is the
identity; compatibility with the mapped automorphism is proof-valued. -/
def app (X : Inertia C) :
    (map (𝟭 C)).obj X ≅ X :=
  Inertia.isoMk (Iso.refl _) (app.comm X)

/-- The underlying forward arrow of the inertia identity comparison is the identity. -/
@[simp]
theorem app.hom.underlying (X : Inertia C) :
    Inertia.hom (app X).hom = 𝟙 X.obj := sorry

/-- The underlying inverse arrow of the inertia identity comparison is the identity. -/
@[simp]
theorem app.inv.underlying (X : Inertia C) :
    Inertia.hom (app X).inv = 𝟙 X.obj := sorry

/-- The explicit identity-comparison components for inertia are natural in inertia morphisms. -/
@[reassoc]
theorem app.naturality {X Y : Inertia C} (f : X ⟶ Y) :
    (map (𝟭 C)).map f ≫ (app Y).hom =
      (app X).hom ≫ f := sorry

/-- The inverse identity-comparison components are natural in inertia morphisms. -/
@[reassoc]
theorem app.inv.naturality {X Y : Inertia C} (f : X ⟶ Y) :
    f ≫ (app Y).inv =
      (app X).inv ≫ (map (𝟭 C)).map f := sorry

end mapIdIso

/-- The canonical componentwise natural isomorphism witnessing identity preservation by inertia. -/
def mapIdIso :
    map (𝟭 C) ≅ 𝟭 (Inertia C) :=
  NatIso.ofComponents
    mapIdIso.app
    (fun f ↦ mapIdIso.app.naturality f)

namespace mapIdIso

/-- The forward component of the inertia identity comparison is its explicit objectwise
comparison. -/
@[simp]
theorem hom.app (X : Inertia C) :
    mapIdIso.hom.app X = (app X).hom := sorry

/-- The inverse component of the inertia identity comparison is the inverse explicit objectwise
comparison. -/
@[simp]
theorem inv.app (X : Inertia C) :
    mapIdIso.inv.app X = (app X).inv := sorry

end mapIdIso

end Inertia
end CategoryTheory
