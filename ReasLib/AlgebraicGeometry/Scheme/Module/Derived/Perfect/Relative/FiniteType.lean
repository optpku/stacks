/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RelativeRestriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Local
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice

/-!
# Relative perfectness over locally finite type scheme morphisms

A derived module is perfect over a locally finite type morphism when it is pseudo-coherent
relative to the base and locally has finite Tor dimension over the inverse-image structure sheaf.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

variable {X S : Scheme.{u}}

/-- Relative perfectness over a locally finite type morphism combines relative
pseudo-coherence with local finite Tor dimension over the inverse-image base sheaf. -/
def perfectOver (f : X ⟶ S) [LocallyOfFiniteType f] :
    ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace) :=
  pseudoCoherentOver f ⊓
    RingedSpace.ModuleDerived.locallyFiniteTorDimension.inverseImage
      (RingedSpace.ModuleDerived.relativeRestriction f.toShHom)

/-- Object-level membership in relative perfectness over a locally finite type morphism. -/
abbrev IsPerfectOver (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) : Prop :=
  perfectOver f E

/-- Relative perfectness over a locally finite type morphism is relative pseudo-coherence
together with local finite Tor dimension over the inverse-image structure sheaf. -/
theorem isPerfectOver_iff (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    IsPerfectOver f E ↔
      IsPseudoCoherentOver f E ∧
        RingedSpace.ModuleDerived.LocallyHasFiniteTorDimension
          ((RingedSpace.ModuleDerived.relativeRestriction f.toShHom).obj E) := sorry

namespace IsPerfectOver

/-- A relatively perfect derived module is pseudo-coherent relative to the base. -/
theorem isPseudoCoherentOver {f : X ⟶ S} [LocallyOfFiniteType f]
    {E : RingedSpace.ModuleDerived X.toRingedSpace} (hE : IsPerfectOver f E) :
    IsPseudoCoherentOver f E := sorry

/-- A relatively perfect derived module locally has finite Tor dimension over the
inverse-image structure sheaf of the base. -/
theorem locallyHasFiniteTorDimension {f : X ⟶ S} [LocallyOfFiniteType f]
    {E : RingedSpace.ModuleDerived X.toRingedSpace} (hE : IsPerfectOver f E) :
    RingedSpace.ModuleDerived.LocallyHasFiniteTorDimension
      ((RingedSpace.ModuleDerived.relativeRestriction f.toShHom).obj E) := sorry

end IsPerfectOver

/-- Relative perfectness over a locally finite type morphism is invariant under isomorphisms
of derived modules. -/
instance perfectOver_isClosedUnderIsomorphisms (f : X ⟶ S)
    [LocallyOfFiniteType f] :
    (perfectOver f).IsClosedUnderIsomorphisms := sorry

namespace IsPerfectOver

/-- Transport relative perfectness over a locally finite type morphism across an isomorphism
of derived modules. -/
theorem ofIso {f : X ⟶ S} [LocallyOfFiniteType f]
    {E E' : RingedSpace.ModuleDerived X.toRingedSpace}
    (hE : IsPerfectOver f E) (e : E ≅ E') : IsPerfectOver f E' := sorry

end IsPerfectOver

/-- Relatively perfect derived modules over a locally finite type morphism form a
triangulated object property. -/
instance perfectOver_isTriangulated (f : X ⟶ S) [LocallyOfFiniteType f] :
    (perfectOver f).IsTriangulated := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
