module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.PropertyP.Resolution
import StacksCheckRecall

@[expose] public section

universe u v w

open DifferentialGradedBimodule

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R) (B : CochainDGAlgebra.{u, w} R)
variable (M : DifferentialGradedBimodule.{u, max v w, v, w} A B)

/- Lemma 22.28.4 (0FQK): every DG `(A, B)`-bimodule admits a quasi-isomorphic property P
resolution by a DG bimodule filtered by shifts of the regular enveloping module. -/
@[stacks 0FQK] #check
  (PropertyP.Resolution.nonempty A B M : Nonempty (PropertyP.Resolution A B M))

#check (HasPropertyP A B : CategoryTheory.ObjectProperty
  (DifferentialGradedBimodule.{u, max v w, v, w} A B))
#check @PropertyP.Resolution.propertyP_obj
