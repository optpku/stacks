module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import ReasLib.Algebra.Homology.ComplexShapeSigns
public import ReasLib.Algebra.Homology.Embedding.Monoidal
public import ReasLib.Algebra.Homology.Embedding.TruncLE
import Mathlib.Tactic.CrossRefAttribute

/-!
# The embedding of natural chain degrees into integer chain degrees

The natural chain-degree embedding includes `down ℕ` in `down ℤ`.  Its underlying embedding is
Mathlib's `ComplexShape.embeddingUpNat.op`, with the source and target ascribed to the canonical
chain shapes so typeclass search sees the intended tensor signs and truncation direction.  This
file owns its monoidal structure and the homology comparison for complexes strictly supported on
its image, including the boundary degree `0`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ComplexShape

/-- The canonical embedding of natural chain degrees into integer chain degrees. -/
@[stacks 09PQ "natural chain degrees inside integer chain degrees"]
def embeddingDownNatInt :
    ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.down ℤ) :=
  ComplexShape.embeddingUpNat.op

namespace embeddingDownNatInt

/-- The natural-to-integer chain embedding preserves and reflects adjacency. -/
instance isRelIff : ComplexShape.embeddingDownNatInt.IsRelIff := sorry

/-- The image of the natural-to-integer chain embedding is a lower truncation region. -/
instance isTruncLE : ComplexShape.embeddingDownNatInt.IsTruncLE := sorry

/-- The natural-to-integer chain embedding is additive. -/
@[stacks 0GZ4 "additivity of the natural-to-integer chain embedding"]
instance isAdditive :
    ComplexShape.Embedding.IsAdditive ComplexShape.embeddingDownNatInt := sorry

/-- The natural-to-integer chain embedding preserves Koszul tensor signs. -/
@[stacks 0GZ4 "tensor signs for the natural-to-integer chain embedding"]
instance preservesTensorSigns :
    ComplexShape.Embedding.PreservesTensorSigns ComplexShape.embeddingDownNatInt := sorry

/-- The additive homomorphism underlying the natural-to-integer chain embedding sends `n` to
`(n : ℤ)`. -/
@[simp]
theorem addMonoidHom_apply (n : ℕ) :
    ComplexShape.Embedding.addMonoidHom ComplexShape.embeddingDownNatInt n = (n : ℤ) := sorry

/-- The tensor sign in integer degree `(n : ℤ)` is the natural chain sign in degree `n`. -/
@[simp]
theorem map_epsilon (n : ℕ) :
    (ComplexShape.down ℤ).ε (ComplexShape.embeddingDownNatInt.f n) =
      (ComplexShape.down ℕ).ε n := sorry

end embeddingDownNatInt

end ComplexShape

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [CategoryWithHomology C]

/-- Restrict an integer-indexed chain complex to its natural chain degrees. -/
abbrev natRestriction (K : ChainComplex C ℤ) : ChainComplex C ℕ :=
  K.restriction ComplexShape.embeddingDownNatInt

/-- A nonnegative integer-indexed chain complex is one strictly supported on its natural-degree
embedding. -/
@[stacks 09PQ "nonnegative support of an integer chain complex"]
abbrev IsNonnegative (K : ChainComplex C ℤ) : Prop :=
  K.IsStrictlySupported ComplexShape.embeddingDownNatInt

/-- The homology of a nonnegative integer-indexed chain complex agrees canonically with the
homology of its natural-degree restriction, including degree `0`. -/
@[stacks 09PQ "homology of the natural restriction of a nonnegative chain complex"]
noncomputable def natRestrictionHomologyIso
    (K : ChainComplex C ℤ) [K.IsNonnegative] (n : ℕ) :
    K.natRestriction.homology n ≅ K.homology (n : ℤ) :=
  (HomologicalComplex.homologyMapIso
      (asIso (K.truncLE'ToRestriction ComplexShape.embeddingDownNatInt)) n).symm ≪≫
    ((K.truncLE' ComplexShape.embeddingDownNatInt).extendHomologyIso
      ComplexShape.embeddingDownNatInt (j := n) (j' := (n : ℤ)) rfl).symm ≪≫
    HomologicalComplex.homologyMapIso
      (K.truncLEIso ComplexShape.embeddingDownNatInt).symm (n : ℤ) ≪≫
    HomologicalComplex.homologyMapIso
      (asIso (K.ιTruncLE ComplexShape.embeddingDownNatInt)) (n : ℤ)

/-- The natural-restriction homology comparison is natural in maps of nonnegative chain
complexes. -/
@[stacks 09PQ "naturality of nonnegative natural-restriction homology"]
theorem natRestrictionHomologyIso_naturality
    {K L : ChainComplex C ℤ} [K.IsNonnegative] [L.IsNonnegative]
    (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap
          (HomologicalComplex.restrictionMap f ComplexShape.embeddingDownNatInt) n ≫
        (L.natRestrictionHomologyIso n).hom =
      (K.natRestrictionHomologyIso n).hom ≫
        HomologicalComplex.homologyMap f (n : ℤ) := sorry

end ChainComplex


#synth ComplexShape.embeddingDownNatInt.IsRelIff
#synth ComplexShape.embeddingDownNatInt.IsTruncLE
#synth ComplexShape.Embedding.IsAdditive ComplexShape.embeddingDownNatInt
#synth ComplexShape.Embedding.PreservesTensorSigns ComplexShape.embeddingDownNatInt

