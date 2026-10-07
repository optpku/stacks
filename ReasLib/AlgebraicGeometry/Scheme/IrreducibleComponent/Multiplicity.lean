module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Length

/-!
# Multiplicities of irreducible components

The multiplicity of an irreducible component of a locally Noetherian scheme is the length of the
ambient local ring at the component's generic point.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The multiplicity of an irreducible component is the length of the ambient local ring at its
generic point. -/
noncomputable def irreducibleComponentMultiplicity (X : Scheme.{u}) [IsLocallyNoetherian X]
    (Z : irreducibleComponents X) : ℕ :=
  (Module.length (X.presheaf.stalk Z.2.1.genericPoint)
    (X.presheaf.stalk Z.2.1.genericPoint)).toNat

/-- The natural-valued multiplicity of an irreducible component coerces to the length of the
ambient local ring at its generic point. -/
theorem coe_irreducibleComponentMultiplicity (X : Scheme.{u}) [IsLocallyNoetherian X]
    (Z : irreducibleComponents X) :
    (X.irreducibleComponentMultiplicity Z : ℕ∞) =
      Module.length (X.presheaf.stalk Z.2.1.genericPoint)
        (X.presheaf.stalk Z.2.1.genericPoint) := sorry

end AlgebraicGeometry.Scheme
