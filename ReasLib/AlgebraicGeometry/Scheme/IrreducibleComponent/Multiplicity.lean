module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Length

/-!
# Multiplicities of irreducible components

The multiplicity of an irreducible component of a locally Noetherian scheme is the length of the
ambient local ring at the component's generic point.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

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

/-- A smooth morphism of locally Noetherian schemes preserves the multiplicity of an
irreducible component whose image is dense in an irreducible component of the target. -/
theorem Hom.irreducibleComponentMultiplicity_eq_of_smooth
    {U X : Scheme.{u}} [IsLocallyNoetherian U] [IsLocallyNoetherian X]
    (f : U ⟶ X) [Smooth f] (T' : irreducibleComponents U)
    (T : irreducibleComponents X)
    (hT : closure (Set.image f.base (T' : Set U)) = (T : Set X)) :
    U.irreducibleComponentMultiplicity T' = X.irreducibleComponentMultiplicity T := sorry

end AlgebraicGeometry.Scheme
