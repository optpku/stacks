/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent

/-!
# Composition of relative pseudo-coherence

Relative pseudo-coherence of derived modules is unchanged when the base is composed with a
pseudo-coherent morphism.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver

/-- For locally finite type morphisms `X ⟶ Y ⟶ S`, if `Y ⟶ S` is pseudo-coherent, then a
derived `𝒪_X`-module is `m`-pseudo-coherent over `Y` exactly when it is `m`-pseudo-coherent
over `S`. -/
theorem iff_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [PseudoCoherent g]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ) :
    IsMPseudoCoherentOver f E m ↔ IsMPseudoCoherentOver (f ≫ g) E m := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver
