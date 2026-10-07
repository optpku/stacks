module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomotopyCofiber
public import ReasLib.CategoryTheory.Homology.ChainShift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopy cofibers of scalar products

For a chain complex of modules, the homotopy cofiber of multiplication by a product `f * g`
is homotopy equivalent to the cofiber of a connecting map from the shifted `f`-cofiber to the
`g`-cofiber.  The connecting map is existential in the source statement, so this leaf exposes the
homotopy-invariant conclusion without choosing noncanonical coordinate data.

@stack 062A
-/

@[expose] public section

open CategoryTheory HomologicalComplex

noncomputable section

universe u

namespace ChainComplex.homotopyCofiber

variable {R : Type u} [CommRing R]

/-- Lemma 15.28.9 (062A): for a chain complex `A` of `R`-modules and `f g : R`, the homotopy
cofiber of multiplication by `f * g` is homotopy equivalent to the cofiber of some map from the
degree-one shift of the `f`-cofiber to the `g`-cofiber. -/
@[stacks 062A "homotopy cofiber of a product scalar"]
theorem exists_homotopyEquiv_smul_mul (A : ChainComplex (ModuleCat R) ℤ) (f g : R) :
    ∃ α : (HomologicalComplex.homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧ ⟶
        HomologicalComplex.homotopyCofiber (g • 𝟙 A),
      Nonempty
        (HomotopyEquiv
          (HomologicalComplex.homotopyCofiber ((f * g) • 𝟙 A))
          (HomologicalComplex.homotopyCofiber α)) := sorry

end ChainComplex.homotopyCofiber
