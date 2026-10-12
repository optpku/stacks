/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening.Universal
public import ReasLib.AlgebraicGeometry.Scheme.Flattening.InDimensions.Representation
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity.Proper

/-!
# Existence of universal flattenings

This module records existence results for universal flattenings of pure and proper families.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Modules
namespace Flattening

/-- A finitely presented module that is pure over the base has a universal flattening
represented by a finitely presented monomorphism. -/
theorem existsMonomorphismRepresentation_of_isPureOver {X S : Scheme.{u}}
    (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation] (h_pure : ℱ.IsPureOver f) :
    ∃ S' : Over S,
      Nonempty ((functor f ℱ).RepresentableBy S') ∧
        Mono S'.hom ∧ Scheme.Hom.FinitePresentation S'.hom := sorry

end Flattening
end Modules

namespace Flattening

/-- A finitely presented morphism whose source is pure over the base has a universal flattening
represented by a finitely presented monomorphism. -/
theorem existsMonomorphismRepresentation_of_isPureOver {X S : Scheme.{u}}
    (f : X ⟶ S) [Scheme.Hom.FinitePresentation f] (h_pure : Scheme.IsPureOver f) :
    ∃ S' : Over S,
      Nonempty
        ((Modules.Flattening.functor f
          (SheafOfModules.unit X.ringCatSheaf : X.Modules)).RepresentableBy S') ∧
        Mono S'.hom ∧ Scheme.Hom.FinitePresentation S'.hom := sorry

end Flattening

namespace Modules
namespace Flattening

/-- For a proper finitely presented morphism, every finitely presented module has a universal
flattening represented by a finitely presented monomorphism. -/
theorem existsMonomorphismRepresentation_of_isProper {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] [Scheme.Hom.FinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation] :
    ∃ S' : Over S,
      Nonempty ((functor f ℱ).RepresentableBy S') ∧
        Mono S'.hom ∧ Scheme.Hom.FinitePresentation S'.hom := sorry

end Flattening
end Modules

namespace Flattening

/-- The structure module of the source of a proper finitely presented morphism has a universal
flattening. -/
theorem isRepresentable_of_isProper {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Scheme.Hom.FinitePresentation f] :
    (Modules.Flattening.functor f
      (SheafOfModules.unit X.ringCatSheaf : X.Modules)).IsRepresentable := sorry

end Flattening
end Scheme
end AlgebraicGeometry
