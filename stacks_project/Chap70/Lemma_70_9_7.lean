module

public import stacks_project.Chap70.Lemma_70_9_7_Integral
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

universe u

/- Lemma 70.9.7 (1): let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated
algebraic space over `S`. Let `A` be an integral quasi-coherent `𝒪_X`-algebra. Then `A` is
the directed colimit of its finite quasi-coherent `𝒪_X`-subalgebras. -/
@[stacks 082C] #check
  (finiteQuasiCoherentSubalgebras_isDirectedColimit_of_isIntegral :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder) [IsIntegral A],
      DirectedOn (· ≤ ·) (finiteQuasiCoherentSubalgebras A) ∧
        IsLUB (finiteQuasiCoherentSubalgebras A) (⊤ : Subobject A.obj))

/- Lemma 70.9.7 (2): let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated
algebraic space over `S`. Let `A` be an integral quasi-coherent `𝒪_X`-algebra. Then `A` is
a directed colimit of finite and finitely presented `𝒪_X`-algebras. -/
@[stacks 082C] #check
  (finiteFinitelyPresentable_ind_of_isIntegral :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder) [IsIntegral A],
      ObjectProperty.ind.{u}
        (fun B : Under (commRingStructureSheaf X) ↦
          finiteProperty X B ∧ finitelyPresentableProperty X B) A.obj)
