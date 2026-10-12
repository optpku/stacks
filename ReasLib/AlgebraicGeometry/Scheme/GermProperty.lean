/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Smooth

/-!
# Properties of scheme germs

This module defines properties of schemes at points and their invariance under morphisms
that are étale or smooth at the selected point.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A property of scheme germs, represented by a property of a scheme at a point. -/
abbrev GermProperty := (X : Scheme.{u}) → X → Prop

namespace GermProperty

/-- Two properties of scheme germs are equal when they are pointwise equivalent. -/
theorem ext {P Q : GermProperty.{u}} (h : ∀ X x, P X x ↔ Q X x) : P = Q := sorry

/-- A property of scheme germs is étale local when it is invariant along every morphism
that is étale at the selected source point. -/
def IsEtaleLocal (P : GermProperty.{u}) : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X),
    f.EtaleAt x → (P Y (f x) ↔ P X x)

/-- Explicit characterization of an étale-local property of scheme germs. -/
theorem isEtaleLocal_iff (P : GermProperty.{u}) :
    P.IsEtaleLocal ↔
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X),
        f.EtaleAt x → (P Y (f x) ↔ P X x) := sorry

/-- Transport an étale-local property across a morphism étale at the selected point. -/
theorem IsEtaleLocal.iff_of {P : GermProperty.{u}} (hP : P.IsEtaleLocal)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (hf : f.EtaleAt x) :
    P Y (f x) ↔ P X x := sorry

/-- A property of scheme germs is smooth local when it is invariant along every morphism
that is smooth at the selected source point. -/
def IsSmoothLocal (P : GermProperty.{u}) : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X),
    f.SmoothAt x → (P Y (f x) ↔ P X x)

/-- Explicit characterization of a smooth-local property of scheme germs. -/
theorem isSmoothLocal_iff (P : GermProperty.{u}) :
    P.IsSmoothLocal ↔
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X),
        f.SmoothAt x → (P Y (f x) ↔ P X x) := sorry

/-- Transport a smooth-local property across a morphism smooth at the selected point. -/
theorem IsSmoothLocal.iff_of {P : GermProperty.{u}} (hP : P.IsSmoothLocal)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (hf : f.SmoothAt x) :
    P Y (f x) ↔ P X x := sorry

/-- Every smooth-local property of scheme germs is étale local. -/
theorem IsSmoothLocal.isEtaleLocal {P : GermProperty.{u}} (hP : P.IsSmoothLocal) :
    P.IsEtaleLocal := sorry

end GermProperty
end AlgebraicGeometry
