/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

-- The discrete-fibration ULift layer owns the bundled lift and canonical projection instance.
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.ULift
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Fibers
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base object for categories fibred in groupoids

The universe-resized identity fibration, its canonical section, and comparison API.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory
open ObjectProperty
open BasedFunctor
open BasedCategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
variable (C) in
/-- The identity fibration on `C`, represented at the universe-closed owner used by canonical
two-fibre products. Its total category and projection use the bundled canonical
`Cat.objULift` owner and `Cat.ObjULift.down`, so no equality between base universes is imposed and
callers need not install a category instance on `ULift C`.

The raw `ofFunctor (𝟭 C)` model does not elaborate here: its functor domain is fixed at object
universe `u`, while this owner requires `max w (max u v)`; Lean does not lift that domain
parameter by type cumulativity. The base category is explicit because this canonical owner has
no value input from which to infer it. -/
@[stacks 02XS "universe-resized identity fibration"]
def base : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C :=
  ofFunctor (Cat.ObjULift.down.{u, v, max w v} C)

/- Axiom audit: the total category and projection of `base` are the explicit
`Cat.objULift` carrier and `Cat.ObjULift.down`. Its `sorryAx` dependency is confined to the
Prop-valued `IsFibered.InGroupoids` owner-membership witness. -/

variable (C) in
/-- The canonical section of the universe-resized identity fibration. Its codomain is expressed
through the bundled owner `base`, so downstream constructions do not need to mention `ULift` or
reconstruct its local category instance. The base category is explicit because this canonical
section has no value input from which to infer it. -/
def baseSection : C ⥤ (base C).total :=
  Cat.ObjULift.up.{u, v, max w v} C

/- Axiom audit: `baseSection` has the explicit non-Prop data of `Cat.ObjULift.up`. Any
`sorryAx` visible through its codomain type comes only from the Prop-valued owner-membership field
of `base`. -/

/-- The canonical section followed by the identity-fibration projection is the identity on `C`. -/
theorem baseSection.comp_projection :
    baseSection C ⋙ (base C).p = 𝟭 C := sorry
/- Proof strategy: unfold `baseSection`, `base`, and the direct owner projections; functor
extensionality reduces the object and morphism components to
`ULift.down (ULift.up x) = x` through the bundled equivalence. -/

/-- The objectwise comparison between the resized identity-fibration section followed by its
projection and the identity functor. Both endpoints reduce to the same base object. -/
def baseSection.projection.appIso (X : C) :
    (baseSection C ⋙ (base C).p).obj X ≅ X :=
  Iso.refl X

/-- The explicit resized identity-fibration comparisons are natural in base morphisms. -/
theorem baseSection.projection.naturality
    {X Y : C} (f : X ⟶ Y) :
    (baseSection C ⋙ (base C).p).map f ≫
        (baseSection.projection.appIso Y).hom =
      (baseSection.projection.appIso X).hom ≫ f := sorry

/-- The canonical natural isomorphism from the resized identity-fibration section followed by
its projection to the identity. Its objectwise non-Prop data are explicit identities. -/
def baseSection.projection.iso :
    baseSection C ⋙ (base C).p ≅ 𝟭 C :=
  NatIso.ofComponents
    (baseSection.projection.appIso.{u, v, w} (C := C))
    (fun f ↦ baseSection.projection.naturality.{u, v, w} f)

/-- The forward component of the resized identity-fibration comparison is its explicit
objectwise identity. -/
@[simp]
theorem baseSection.projection.iso.hom.app (X : C) :
    (baseSection.projection.iso.{u, v, w} (C := C)).hom.app X =
      (baseSection.projection.appIso.{u, v, w} X).hom := sorry

/-- The inverse component of the resized identity-fibration comparison is its explicit
objectwise identity. -/
@[simp]
theorem baseSection.projection.iso.inv.app (X : C) :
    (baseSection.projection.iso.{u, v, w} (C := C)).inv.app X =
      (baseSection.projection.appIso.{u, v, w} X).inv := sorry

variable {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}

/-- The equality over `C` used by the canonical morphism from `X` to the
universe-resized identity fibration.

Proof strategy: reassociate composition, rewrite with `baseSection.comp_projection`, and finish
with the right-identity law for `X.p`. -/
theorem baseProjection.comm
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C) :
    (X.p ⋙ baseSection C) ⋙ (base C).p = X.p := sorry

/-- The canonical projection comparison for the universe-resized identity fibration. It is
assembled from associativity, the explicit section-projection comparison, and the right unitor,
rather than generated from the derived strict equality `baseProjection.comm`. -/
def baseProjection.iso
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C) :
    (X.p ⋙ baseSection C) ⋙ (base C).p ≅ X.p :=
  Functor.associator X.p (baseSection C) (base C).p ≪≫
    Functor.isoWhiskerLeft X.p (baseSection.projection.iso.{u, v, w} (C := C)) ≪≫
      Functor.rightUnitor X.p

/-- The object component of the canonical base-projection comparison is the explicit
section-projection comparison at the corresponding base object. -/
@[simp]
theorem baseProjection.iso.app
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C) (x : X.total) :
    (baseProjection.iso X).app x =
      baseSection.projection.appIso.{u, v, w} (X.p.obj x) := sorry

/-- The forward object component of the canonical base-projection comparison is the explicit
section-projection component. -/
@[simp]
theorem baseProjection.iso.hom.app
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C) (x : X.total) :
    (baseProjection.iso X).hom.app x =
      (baseSection.projection.appIso.{u, v, w} (X.p.obj x)).hom := sorry

/-- The inverse object component of the canonical base-projection comparison is the inverse
explicit section-projection component. -/
@[simp]
theorem baseProjection.iso.inv.app
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C) (x : X.total) :
    (baseProjection.iso X).inv.app x =
      (baseSection.projection.appIso.{u, v, w} (X.p.obj x)).inv := sorry

/-- The canonical morphism from a category fibred in groupoids over `C` to the terminal identity
fibration. Its underlying functor is `X.p ⋙ baseSection`; the target is resized only enough
to inhabit the same universe-closed bicategory as `X`. -/
def baseProjection
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C) :
    X ⟶ base C :=
  ofBasedFunctor
    (BasedFunctor.ofFunctor (X.p ⋙ baseSection C) (baseProjection.comm X))

/- Axiom audit: the underlying total-category functor of `baseProjection X` is explicitly
`X.p ⋙ baseSection`. Its `sorryAx` dependency is confined to the Prop-valued commuting law
`baseProjection.comm X` and the target owner-membership proof inherited from `base`. -/

end FiberedCategoryOver.Groupoids

end CategoryTheory
