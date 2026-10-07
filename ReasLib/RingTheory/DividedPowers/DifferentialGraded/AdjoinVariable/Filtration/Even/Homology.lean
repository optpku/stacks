module

public import ReasLib.Algebra.Homology.Embedding.DownNat.Homology
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.NatRestriction.Homology
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.AdjoinVariable.Filtration.Even
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology comparison for the exponent filtration on an even cell

The exponent filtration is defined on the natural-degree chain complex and then extended to a
cochain complex by `ComplexShape.embeddingDownNat`.  This leaf records the resulting comparison
with the original integer-graded chain-DGA homology, including the sign reindexing.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace DividedPowerChainAlgebra.Adjoin.Even.Extension.ExponentFiltration

variable {R : Type u} [CommRing R]
variable {A : DividedPowerChainAlgebra.{u, v} R} {d : ℕ+}
variable {f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}

/-- The cochain homology of the exponent-filtered even cell in degree `-(n : ℤ)` is canonically
the chain-DGA homology in natural degree `n`. -/
@[stacks 0GZ6 "sign-reindexed homology of the even-cell filtered complex"]
noncomputable def filteredComplexHomologyIso (X : Even.Extension A d f) (n : ℕ) :
    (filteredComplex X).underlying.homology (-(n : ℤ)) ≅
      X.algebra.toChainDGAlgebra.homology (n : ℤ) :=
  eqToIso (congrArg
      (fun K ↦ K.homology (-(n : ℤ)))
      (filteredComplex_underlying X)) ≪≫
    ChainComplex.extendDownNatHomologyIso X.algebra.toChainDGAlgebra.natRestriction n ≪≫
    X.algebra.toChainDGAlgebra.natRestrictionHomologyIso n

end DividedPowerChainAlgebra.Adjoin.Even.Extension.ExponentFiltration
