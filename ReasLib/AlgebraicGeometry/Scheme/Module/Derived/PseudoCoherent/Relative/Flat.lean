module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.Flat

/-!
# Relative pseudo-coherence over flat locally finitely presented morphisms
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver

/-- Composing the base with a flat, locally finitely presented morphism does not change
relative `m`-pseudo-coherence of a derived module. -/
theorem comp_iff_of_flat_of_locallyOfFinitePresentation
    {X T S : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S)
    [LocallyOfFiniteType f] [Flat g] [LocallyOfFinitePresentation g]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ) :
    IsMPseudoCoherentOver (f ≫ g) E m ↔ IsMPseudoCoherentOver f E m := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- For a closed immersion into a scheme flat and locally of finite presentation over a base,
relative pseudo-coherence of a derived module, relative pseudo-coherence of its pushforward,
and absolute pseudo-coherence of its pushforward are equivalent. -/
theorem mPseudoCoherent_pushforward_tfae
    {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    [IsClosedImmersion i] [Flat p] [LocallyOfFinitePresentation p]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ) :
    List.TFAE [
      IsMPseudoCoherentOver (i ≫ p) E m,
      IsMPseudoCoherentOver p
        ((RingedSpace.moduleDerivedPushforward i.toShHom).obj E) m,
      RingedSpace.ModuleDerived.IsMPseudoCoherent
        ((RingedSpace.moduleDerivedPushforward i.toShHom).obj E) m
    ] := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
