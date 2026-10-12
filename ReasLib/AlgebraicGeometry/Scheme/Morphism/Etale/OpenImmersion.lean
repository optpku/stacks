/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Open immersions from étale morphisms

This file records a criterion for an étale morphism to be an open immersion.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsOpenImmersion

/-- A universally injective étale morphism of schemes is an open immersion. -/
@[instance]
theorem of_etale_of_universallyInjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Etale f] [UniversallyInjective f] : IsOpenImmersion f := sorry

end AlgebraicGeometry.IsOpenImmersion

namespace AlgebraicGeometry

/-- For a morphism of schemes, being an open immersion, being universally injective and
étale, and being a flat monomorphism locally of finite presentation are equivalent. -/
theorem tfae_openImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) :
    List.TFAE [
      IsOpenImmersion f,
      UniversallyInjective f ∧ Etale f,
      Flat f ∧ Mono f ∧ LocallyOfFinitePresentation f] := sorry

end AlgebraicGeometry
