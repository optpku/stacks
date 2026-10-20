module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.Monoidal
public import ReasLib.Algebra.Homology.CochainDGAlgebra.KFlat
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Monoidal Characterization of K-Flat Cochain Differential Graded Algebras

This compatibility leaf identifies ring-relative DGA K-flatness with K-flatness for the
ambient monoidal tensor product when the DGA carrier lives in the ground-ring universe.
@stack 06XZ
-/

noncomputable section

universe u

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]

/-- In the carrier universe of the ground ring, DGA K-flatness agrees with K-flatness for the
monoidal tensor product on `ModuleCat R`. -/
@[stacks 06XZ "monoidal characterization of DGA K-flatness"]
theorem isKFlat_iff_monoidal (A : CochainDGAlgebra.{u, u} R) :
    A.IsKFlat ↔ A.toCochainComplex.IsKFlat := sorry

end CochainDGAlgebra
