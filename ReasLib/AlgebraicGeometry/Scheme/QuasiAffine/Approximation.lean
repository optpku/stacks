module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Approximation of quasi-affine schemes

Finite type subalgebras of an affine ambient ring can preserve a given open immersion and
exhaust that ring under inclusion.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {W : Scheme.{u}} {R : Type u} [CommRing R]

/-- The finite type `ℤ`-subalgebras of `R` for which the map induced by an open immersion
`W ⟶ Spec(R)` remains an open immersion into the smaller spectrum. -/
def finiteTypeZSubalgebraStages (f : W ⟶ Spec (CommRingCat.of R)) : Set (Subalgebra ℤ R) :=
  {A | Algebra.FiniteType ℤ A ∧
    IsOpenImmersion (f ≫ Spec.map (CommRingCat.ofHom A.val.toRingHom))}

/-- Membership in `finiteTypeZSubalgebraStages f` means finite type over `ℤ` together with
the open-immersion property for the induced map to the smaller spectrum. -/
theorem mem_finiteTypeZSubalgebraStages
    (f : W ⟶ Spec (CommRingCat.of R)) (A : Subalgebra ℤ R) :
    A ∈ finiteTypeZSubalgebraStages f ↔
      Algebra.FiniteType ℤ A ∧
        IsOpenImmersion (f ≫ Spec.map (CommRingCat.ofHom A.val.toRingHom)) :=
  Iff.rfl

/-- An open immersion from a scheme of finite type over `ℤ` into an affine scheme is induced
from an open immersion over some finite type `ℤ`-subalgebra of the ambient ring. -/
theorem finiteTypeZSubalgebraStages_nonempty
    (f : W ⟶ Spec (CommRingCat.of R)) [IsOpenImmersion f]
    [FiniteType (specULiftZIsTerminal.from W)] :
    (finiteTypeZSubalgebraStages f).Nonempty := sorry

/-- The finite type `ℤ`-subalgebras preserving an open immersion from a scheme of finite type
over `ℤ` are directed under inclusion and have supremum equal to the ambient ring. -/
theorem finiteTypeZSubalgebraStages_directed_and_sSup_eq_top
    (f : W ⟶ Spec (CommRingCat.of R)) [IsOpenImmersion f]
    [FiniteType (specULiftZIsTerminal.from W)] :
    DirectedOn (· ≤ ·) (finiteTypeZSubalgebraStages f) ∧
      sSup (finiteTypeZSubalgebraStages f) = ⊤ := sorry

end AlgebraicGeometry.Scheme.Hom
