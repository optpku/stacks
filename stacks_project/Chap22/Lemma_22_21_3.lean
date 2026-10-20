module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyI.Embedding
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)
variable (M : DifferentialGradedModule.{u, v} A)

/- Lemma 22.21.3 (09KT): every right DG `A`-module admits a two-step property `(I)` embedding,
monic both on its underlying graded module and on incoming-differential cokernels. -/
@[stacks 09KT] #check
  (DifferentialGradedModule.PropertyI.Embedding.nonempty A M :
    Nonempty (DifferentialGradedModule.PropertyI.Embedding A M))
