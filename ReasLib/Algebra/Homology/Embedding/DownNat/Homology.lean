/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.Embedding.DownNat
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology of the standard chain-to-cochain extension

The embedding `ComplexShape.embeddingDownNat` places a natural chain degree `n` in cochain
degree `-(n : ℤ)`.  This leaf exposes the corresponding homology comparison independently of
any differential graded algebra or filtration construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The homology of a natural chain complex, viewed after extension by zero in cochain degrees,
is canonically its homology in degree `n`. -/
@[stacks 0FP8 "homology of the standard chain-to-cochain extension"]
noncomputable def extendDownNatHomologyIso
    (K : ChainComplex C ℕ) (n : ℕ)
    [K.HasHomology n]
    [(K.extend ComplexShape.embeddingDownNat).HasHomology (-(n : ℤ))] :
    (K.extend ComplexShape.embeddingDownNat).homology (-(n : ℤ)) ≅ K.homology n :=
  K.extendHomologyIso ComplexShape.embeddingDownNat (j := n)
    (j' := -(n : ℤ)) rfl

/-- The standard chain-to-cochain homology comparison is natural in maps of chain complexes. -/
@[reassoc, stacks 0FP8 "naturality of the standard chain-to-cochain homology comparison"]
theorem extendDownNatHomologyIso_naturality
    {K L : ChainComplex C ℕ} (f : K ⟶ L) (n : ℕ)
    [K.HasHomology n] [L.HasHomology n]
    [(K.extend ComplexShape.embeddingDownNat).HasHomology (-(n : ℤ))]
    [(L.extend ComplexShape.embeddingDownNat).HasHomology (-(n : ℤ))] :
    HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap f ComplexShape.embeddingDownNat) (-(n : ℤ)) ≫
        (L.extendDownNatHomologyIso n).hom =
      (K.extendDownNatHomologyIso n).hom ≫ HomologicalComplex.homologyMap f n := sorry

end ChainComplex
