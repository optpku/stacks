module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective

/-! # Étale open immersions of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale

/-- An open immersion of algebraic spaces is étale. -/
instance ofIsOpenImmersion {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [h : IsOpenImmersion f] : Etale f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Etale

namespace AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion

/-- An étale and universally injective morphism of algebraic spaces is an open immersion. -/
@[instance]
theorem of_etale_of_universallyInjective {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] [UniversallyInjective f] : IsOpenImmersion f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion
