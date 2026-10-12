/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap38.«38_20_3_2_FlatFunctor»
public import ReasLib.RingTheory.Flat.LocalAlgebra.Flattening.BaseChange
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u v w

namespace LocalAlgCat.Flattening

variable (A : Type u) (B C : Type v) (M : Type w)
variable [CommRing A] [IsLocalRing A]
variable [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
variable [IsLocalHom (algebraMap B C)] [Module.Flat B C]
variable [AddCommGroup M] [Module B M]

/- Lemma 38.20.6: extending `M` along a flat local map `B ⟶ C` of local
`A`-algebras does not change its flattening functor. -/
@[stacks 05P5] #check
  (LocalAlgCat.Flattening.functor_eq_baseChange A B C M :
    LocalAlgCat.Flattening.functor A B M =
      LocalAlgCat.Flattening.functor A C (C ⊗[B] M))

end LocalAlgCat.Flattening
