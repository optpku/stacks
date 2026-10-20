module

public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import ReasLib.Algebra.Homology.ChainComplex.Monoidal.Symmetric
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Monoid
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.NatRestriction
public import ReasLib.Algebra.Homology.Embedding.UpNat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Chain DGAs from nonnegative chain monoids

The canonical embedding `ComplexShape.embeddingDownNatInt` sends `n : ℕ` to the same integer
chain degree `(n : ℤ)`. Its extension-by-zero functor is monoidal, so it transports monoids in
nonnegative chain complexes to monoids in integer-indexed chain complexes. Recovering the
homogeneous operations then gives an elementary `ChainDGAlgebra` without choosing any carrier,
unit, multiplication, or map.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace ChainDGAlgebra

/-- Extend a monoid in nonnegative chain complexes to integer chain degrees and recover its chain
differential graded algebra. -/
@[stacks 0GZ4 "nonnegative chain monoids as integer chain DGAs"]
noncomputable def fromChainMon (R : Type u) [CommRing R] :
    Mon (ChainComplex (ModuleCat.{u} R) ℕ) ⥤ ChainDGAlgebra R :=
  (natEmbedding.extendFunctor (ModuleCat.{u} R)).mapMon ⋙ ofMonFunctor R

/-- Extend a commutative monoid in nonnegative chain complexes to an integer-graded chain DGA. -/
@[stacks 0GZ4 "nonnegative chain commutative monoids as integer chain DGAs"]
noncomputable def fromChainCommMon (R : Type u) [CommRing R] :
    CommMon (ChainComplex (ModuleCat.{u} R) ℕ) ⥤ ChainDGAlgebra R :=
  CommMon.forget₂Mon (ChainComplex (ModuleCat.{u} R) ℕ) ⋙ fromChainMon R

/-- The underlying integer chain complex produced from a nonnegative chain monoid is extension by
zero along `natEmbedding`. -/
@[simp]
theorem fromChainMon_obj_toChainComplex
    {R : Type u} [CommRing R]
    (A : Mon (ChainComplex (ModuleCat.{u} R) ℕ)) :
    ((fromChainMon R).obj A).toChainComplex = A.X.extend natEmbedding := sorry

/-- On morphisms, `fromChainMon` extends the underlying nonnegative chain map. -/
@[simp]
theorem fromChainMon_map_toChainMap
    {R : Type u} [CommRing R]
    {A B : Mon (ChainComplex (ModuleCat.{u} R) ℕ)} (f : A ⟶ B) :
    ((fromChainMon R).map f).toChainMap =
      (natEmbedding.extendFunctor (ModuleCat.{u} R)).map f.hom := sorry

/-- The underlying integer chain complex produced from a nonnegative chain commutative monoid is
extension by zero along `natEmbedding`. -/
@[simp]
theorem fromChainCommMon_obj_toChainComplex
    {R : Type u} [CommRing R]
    (A : CommMon (ChainComplex (ModuleCat.{u} R) ℕ)) :
    ((fromChainCommMon R).obj A).toChainComplex = A.X.extend natEmbedding := sorry

/-- On morphisms, `fromChainCommMon` extends the underlying nonnegative chain map while retaining
its unit and multiplication. -/
@[simp]
theorem fromChainCommMon_map_toChainMap
    {R : Type u} [CommRing R]
    {A B : CommMon (ChainComplex (ModuleCat.{u} R) ℕ)} (f : A ⟶ B) :
    ((fromChainCommMon R).map f).toChainMap =
      (natEmbedding.extendFunctor (ModuleCat.{u} R)).map f.hom.hom := sorry

#synth ComplexShape.Embedding.IsAdditive ComplexShape.embeddingDownNatInt
#synth ComplexShape.Embedding.PreservesTensorSigns ComplexShape.embeddingDownNatInt

-- Both functors are explicit compositions. Any `sorryAx` dependency is confined to the
-- proposition-valued monoidal coherence, DGA-law, and functoriality fields.

end ChainDGAlgebra
