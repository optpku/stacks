module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Fiber

/-!
# Fibres of étale morphisms

This file characterizes étale schemes over a field and describes the fibres of
arbitrary étale morphisms.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A scheme over a field is étale over that field if and only if it admits a presentation as a
coproduct of spectra of finite separable field extensions. -/
theorem etale_iff_schemeAsDisjointUnionOfSpecFiniteSeparable
    {k : Type u} [Field k] (X : SchemeOverField k) :
    Etale X.hom ↔ Nonempty (SchemeAsDisjointUnionOfSpecFiniteSeparable k X) := sorry

/-- Every fibre of an étale morphism admits a presentation as a coproduct of spectra of finite
separable extensions of the corresponding residue field. -/
theorem fiber_schemeAsDisjointUnionOfSpecFiniteSeparable_of_etale
    {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] (s : S) :
    Nonempty
      (SchemeAsDisjointUnionOfSpecFiniteSeparable (S.residueField s)
        (Over.mk (f.fiberOverSpecResidueField s).hom)) := sorry

/-- A flat, locally finitely presented morphism whose residue-field fibres are coproducts of
spectra of finite separable field extensions is étale. -/
theorem Scheme.Hom.etale_of_flat_of_finiteSeparableFibers
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (hfiber : f.FibersAreDisjointUnionOfSpecFiniteSeparable) : Etale f := sorry

/-- An étale morphism induces an étale morphism between the spectra of the
residue fields at a point and its image. -/
instance Etale.specMap_residueFieldMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Etale f] (x : X) : Etale (Spec.map (f.residueFieldMap x)) := sorry

/-- The morphism between fibres induced by a commutative square with étale
vertical arrows is étale. -/
instance Scheme.Hom.fiberMap_etale {X' S' X S : Scheme.{u}}
    (f' : X' ⟶ S') (i : X' ⟶ X) (g : S' ⟶ S) (f : X ⟶ S)
    [Etale i] [Etale g] (sq : CommSq i f' f g) (s' : S') :
    Etale (Scheme.Hom.fiberMap f' i g f sq s') := sorry

namespace Etale

/-- Given a commutative square with étale vertical arrows, the induced
morphism from the fibre over a point to the fibre over its specified image is
étale. -/
theorem fiberMap_of_commSq {X' S' X S : Scheme.{u}}
    (f' : X' ⟶ S') (i : X' ⟶ X) (g : S' ⟶ S) (f : X ⟶ S)
    [Etale i] [Etale g] (sq : CommSq i f' f g) (s' : S') (s : S)
    (hs : g s' = s) :
    Etale (hs ▸ Scheme.Hom.fiberMap f' i g f sq s') := sorry

end Etale

end AlgebraicGeometry
