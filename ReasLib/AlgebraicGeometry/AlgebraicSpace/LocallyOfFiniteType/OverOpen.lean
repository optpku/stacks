module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Algebraic spaces locally of finite type and isomorphic over an open

These spaces form a full subcategory of algebraic spaces over the base scheme.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is locally of finite type over its base when the structural morphism
of every representable étale scheme chart is locally of finite type. -/
def IsLocallyOfFiniteTypeOver {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop :=
  ∀ (T : Over S) (p : yoneda.obj T ⟶ X.functorOfPoints),
    (MorphismProperty.over (@Etale)).presheaf p → LocallyOfFiniteType T.hom

/-- An algebraic space is isomorphic to its base over an open when its restricted functor of
points has an invertible morphism to the terminal presheaf. -/
def IsIsoOverSchemeOpen {S : Scheme.{u}} (X : AlgebraicSpace S) (U : S.Opens) : Prop :=
  IsIso (Functor.whiskerLeft (Over.map U.ι).op (Limits.terminal.from X.functorOfPoints))

/-- The property of being locally of finite type over the base and isomorphic to it over
the specified open. -/
def locallyOfFiniteTypeOverOpenProperty {S : Scheme.{u}} (U : S.Opens) :
    ObjectProperty (AlgebraicSpace S) :=
  fun X ↦ IsLocallyOfFiniteTypeOver X ∧ IsIsoOverSchemeOpen X U

/-- Membership in the open-isomorphism property means that every representable étale scheme
chart is locally of finite type over the base and the restricted terminal map is invertible. -/
theorem locallyOfFiniteTypeOverOpenProperty_iff {S : Scheme.{u}} (U : S.Opens)
    (X : AlgebraicSpace S) :
    locallyOfFiniteTypeOverOpenProperty U X ↔
      (∀ (T : Over S) (p : yoneda.obj T ⟶ X.functorOfPoints),
        (MorphismProperty.over (@Etale)).presheaf p → LocallyOfFiniteType T.hom) ∧
      IsIso (Functor.whiskerLeft (Over.map U.ι).op (Limits.terminal.from X.functorOfPoints)) := sorry

/-- The full subcategory of algebraic spaces locally of finite type over the base and
isomorphic to it over a specified open. -/
abbrev LocallyOfFiniteTypeOverOpen {S : Scheme.{u}} (U : S.Opens) :=
  (locallyOfFiniteTypeOverOpenProperty U).FullSubcategory

namespace LocallyOfFiniteTypeOverOpen

/-- The inclusion of spaces locally of finite type and isomorphic over an open into all
algebraic spaces over the base. -/
def inclusion {S : Scheme.{u}} (U : S.Opens) :
    LocallyOfFiniteTypeOverOpen U ⥤ AlgebraicSpace S :=
  (locallyOfFiniteTypeOverOpenProperty U).ι

/-- Construct an object of the full subcategory from an algebraic space and evidence of local
finite type and of being isomorphic to the base over the open. -/
def of {S : Scheme.{u}} (U : S.Opens) (X : AlgebraicSpace S)
    (hX : locallyOfFiniteTypeOverOpenProperty U X) : LocallyOfFiniteTypeOverOpen U :=
  ⟨X, hX⟩

end LocallyOfFiniteTypeOverOpen

end AlgebraicGeometry.AlgebraicSpace
