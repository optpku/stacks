module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.WeaklyEtale

/-- A flat monomorphism of schemes is weakly étale. -/
instance (priority := 900) instOfFlatOfMono {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [Mono f] : WeaklyEtale f := sorry

/-- An open immersion of schemes is weakly étale. -/
theorem of_isOpenImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] : WeaklyEtale f :=
  AlgebraicGeometry.WeaklyEtale.instOfEtale f

/-- A flat unramified morphism of schemes is weakly étale. -/
instance (priority := 900) instOfFlatOfUnramified {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [Unramified f] : WeaklyEtale f := sorry

/-- An étale morphism of schemes is weakly étale. -/
theorem of_etale {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Etale f] : WeaklyEtale f :=
  AlgebraicGeometry.WeaklyEtale.instOfEtale f

end AlgebraicGeometry.WeaklyEtale
