module

public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over

/-!
# Finite-presentation morphisms that are isomorphisms over an open

This leaf owns the slice subcategory of finite-presentation morphisms that
become isomorphisms after restriction to a specified open subset. Its
historical `pullback` compatibility functor assumes that the base-change
morphism is an isomorphism over that open. The unrestricted base-change and
open-restriction API lives in `IsoOverOpen.BaseChange`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/-- A scheme morphism is of finite presentation and becomes an isomorphism after restriction to
an open subset of its target. -/
abbrev IsFinitePresentationIsoOverOpen
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) : Prop :=
  FinitePresentation f ∧ IsIso (f ∣_ U)

end Scheme.Hom

/-- The object property on `Over S` selecting finite-presentation morphisms that are
isomorphisms over the chosen open `U`. -/
abbrev finitePresentationIsoOverOpenProperty
    {S : Scheme.{u}} (U : S.Opens) : ObjectProperty (Over S) :=
  fun X ↦ X.hom.IsFinitePresentationIsoOverOpen U

/-- The full subcategory of schemes of finite presentation over `S` that are isomorphisms over
the chosen open `U`. -/
abbrev FinitePresentationIsoOverOpen
    {S : Scheme.{u}} (U : S.Opens) : Type (u + 1) :=
  (finitePresentationIsoOverOpenProperty U).FullSubcategory

namespace FinitePresentationIsoOverOpen

/-- The inclusion of `FinitePresentationIsoOverOpen U` into the ambient category `Over S`. -/
abbrev inclusion
    {S : Scheme.{u}} (U : S.Opens) : FinitePresentationIsoOverOpen U ⥤ Over S :=
  (finitePresentationIsoOverOpenProperty U).ι

/-- The structural morphism of an object of `FinitePresentationIsoOverOpen U` is of finite
presentation. -/
theorem finitePresentation_hom
    {S : Scheme.{u}} (U : S.Opens) (X : FinitePresentationIsoOverOpen U) :
    Scheme.Hom.FinitePresentation X.obj.hom := sorry

/-- The structural morphism of an object of `FinitePresentationIsoOverOpen U` is canonically
of finite presentation. -/
instance instFinitePresentationHom
    {S : Scheme.{u}} (U : S.Opens) (X : FinitePresentationIsoOverOpen U) :
    Scheme.Hom.FinitePresentation X.obj.hom := sorry

/-- The structural morphism of an object of `FinitePresentationIsoOverOpen U` becomes an
isomorphism after restriction to `U`. -/
theorem isIso_restrict_hom
    {S : Scheme.{u}} (U : S.Opens) (X : FinitePresentationIsoOverOpen U) :
    IsIso (X.obj.hom ∣_ U) := sorry

/-- Restricting the structural morphism of an object of `FinitePresentationIsoOverOpen U` to
`U` is canonically an isomorphism. -/
instance instIsIsoRestrictHom
    {S : Scheme.{u}} (U : S.Opens) (X : FinitePresentationIsoOverOpen U) :
    IsIso (X.obj.hom ∣_ U) := sorry

/-- Compatibility form of pullback preservation, for callers that additionally know that the
base-change morphism is an isomorphism over `U`. The unrestricted form is
`Scheme.Hom.isFinitePresentationIsoOverOpen_pullback_snd` in `IsoOverOpen.BaseChange`. -/
theorem isFinitePresentationIsoOverOpen_pullback
    {S W : Scheme.{u}} (s : W ⟶ S) (U : S.Opens)
    (hs : IsIso (s ∣_ U))
    (X : Over S) (hX : finitePresentationIsoOverOpenProperty U X) :
    finitePresentationIsoOverOpenProperty (s ⁻¹ᵁ U) ((Over.pullback s).obj X) := sorry

/-- Compatibility pullback functor along a morphism that is an isomorphism over `U`. For
arbitrary base change use the proposition-level
`Scheme.Hom.isFinitePresentationIsoOverOpen_pullback_snd` from `IsoOverOpen.BaseChange`. -/
noncomputable def pullback
    {S W : Scheme.{u}} (s : W ⟶ S) (U : S.Opens)
    (hs : IsIso (s ∣_ U)) :
    FinitePresentationIsoOverOpen U ⥤ FinitePresentationIsoOverOpen (s ⁻¹ᵁ U) :=
  ObjectProperty.lift
    (finitePresentationIsoOverOpenProperty (s ⁻¹ᵁ U))
    ((inclusion U) ⋙ Over.pullback s)
    (fun X ↦ isFinitePresentationIsoOverOpen_pullback s U hs X.obj X.property)

end FinitePresentationIsoOverOpen

end AlgebraicGeometry
