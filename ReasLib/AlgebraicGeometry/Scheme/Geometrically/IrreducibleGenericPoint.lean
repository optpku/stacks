/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.Topology.Sober
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Closure

/-!
# Generic-point criteria for geometric irreducibility

This leaf relates geometric irreducibility of an irreducible scheme over a
field to the residue field at a chosen generic point.  The induced field
algebra is the canonical `Scheme.Hom.ResidueField.algebraOfSpec` owner.
-/

@[expose] public section

open AlgebraicGeometry CommRingCat
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace GeometricallyIrreducible.GenericPoint

section

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- For an irreducible scheme, geometric irreducibility is equivalent to geometric irreducibility
of the residue-field spectrum at any chosen generic point. -/
theorem iff_residueField
    [IrreducibleSpace X] (ξ : X) (hξ : ξ ∈ genericPoints X) :
    GeometricallyIrreducible f ↔
      GeometricallyIrreducible
        (Spec.map (CommRingCat.ofHom
          (Scheme.Hom.ResidueField.mapOfSpec f ξ))) := sorry

namespace ResidueField

/-- At a generic point of an irreducible scheme, geometric irreducibility of the residue-field
spectrum is equivalent to triviality of the separable closure of the base field. -/
theorem iff_separableClosure_eq_bot
    [IrreducibleSpace X] (ξ : X) (hξ : ξ ∈ genericPoints X) :
      GeometricallyIrreducible
        (Spec.map (CommRingCat.ofHom
          (Scheme.Hom.ResidueField.mapOfSpec f ξ))) ↔
      Scheme.Hom.ResidueField.separableClosureOfSpec f ξ = ⊥ := sorry

end ResidueField

end

end GeometricallyIrreducible.GenericPoint

end AlgebraicGeometry
