/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.ChainComplex.Monoidal.Symmetric
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Monoid
public import ReasLib.Algebra.Homology.Embedding.DownNat
public import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cochain DGAs from nonnegative chain monoids

Extension by zero along `ComplexShape.embeddingDownNat` is monoidal.  It therefore transports a
monoid in nonnegative chain complexes to a monoid in integer cochain complexes, after which
`CochainDGAlgebra.ofMonFunctor` recovers its elementary cochain-DGA presentation.  The commutative
variant first forgets only commutativity, retaining the full multiplication and unit.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CochainDGAlgebra

/-- Extend a monoid in nonnegative chain complexes to integer cochain degrees and recover its
cochain differential graded algebra. -/
@[stacks 0GZJ "nonnegative chain monoids as cochain DGAs"]
noncomputable def fromChainMon (R : Type u) [CommRing R] :
    Mon (ChainComplex (ModuleCat.{u} R) ℕ) ⥤ CochainDGAlgebra R :=
  (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} R)).mapMon ⋙
    ofMonFunctor R

/-- Extend a commutative monoid in nonnegative chain complexes to an integer-graded cochain DGA. -/
@[stacks 0GZJ "nonnegative chain commutative monoids as cochain DGAs"]
noncomputable def fromChainCommMon (R : Type u) [CommRing R] :
    CommMon (ChainComplex (ModuleCat.{u} R) ℕ) ⥤ CochainDGAlgebra R :=
  CommMon.forget₂Mon (ChainComplex (ModuleCat.{u} R) ℕ) ⋙ fromChainMon R

/-- The underlying cochain complex produced from a chain monoid is its extension by zero along
`ComplexShape.embeddingDownNat`. -/
@[simp]
theorem fromChainMon_obj_toCochainComplex
    {R : Type u} [CommRing R]
    (A : Mon (ChainComplex (ModuleCat.{u} R) ℕ)) :
    ((fromChainMon R).obj A).toCochainComplex =
      A.X.extend ComplexShape.embeddingDownNat := sorry

/-- On morphisms, `fromChainMon` uses the extension of the underlying chain map. -/
@[simp]
theorem fromChainMon_map_toCochainMap
    {R : Type u} [CommRing R]
    {A B : Mon (ChainComplex (ModuleCat.{u} R) ℕ)} (f : A ⟶ B) :
    ((fromChainMon R).map f).toCochainMap =
      (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} R)).map f.hom := sorry

/-- The underlying cochain complex produced from a chain commutative monoid is its extension by
zero along `ComplexShape.embeddingDownNat`. -/
@[simp]
theorem fromChainCommMon_obj_toCochainComplex
    {R : Type u} [CommRing R]
    (A : CommMon (ChainComplex (ModuleCat.{u} R) ℕ)) :
    ((fromChainCommMon R).obj A).toCochainComplex =
      A.X.extend ComplexShape.embeddingDownNat := sorry

/-- On morphisms, `fromChainCommMon` extends the underlying chain map and forgets no algebraic
data except commutativity. -/
@[simp]
theorem fromChainCommMon_map_toCochainMap
    {R : Type u} [CommRing R]
    {A B : CommMon (ChainComplex (ModuleCat.{u} R) ℕ)} (f : A ⟶ B) :
    ((fromChainCommMon R).map f).toCochainMap =
      (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} R)).map f.hom.hom := sorry

-- Both functors are explicit compositions; their only `sorryAx` dependencies come from the
-- already-separated monoidal coherence and DGA-law fields.

end CochainDGAlgebra
