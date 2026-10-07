module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.QuasiIso.Derived
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}
variable (f : A ⟶ B) (hf : CochainDGAlgebra.quasiIso f)

/- Lemma 22.37.1 (09S6): a quasi-isomorphism of differential graded algebras induces an
`R`-linear triangulated equivalence between the canonical derived categories of right
differential graded modules, with derived restriction of scalars as inverse. -/
@[stacks 09S6] #check
  (CochainDGAlgebra.Hom.Derived.triangulatedEquivalence f hf :
    RLinear.TriangulatedEquivalence R
      (DifferentialGradedModule.Derived.Category A)
      (DifferentialGradedModule.Derived.Category B))

#check @CochainDGAlgebra.Hom.Derived.equivalence
#check @CochainDGAlgebra.Hom.Derived.equivalence_functor
#check @CochainDGAlgebra.Hom.Derived.equivalence_inverse
#check @CochainDGAlgebra.Hom.Derived.triangulatedEquivalence_functor
#check @CochainDGAlgebra.Hom.Derived.triangulatedEquivalence_inverse
#check @CochainDGAlgebra.Hom.Derived.extension_isEquivalence
#check @CochainDGAlgebra.Hom.Derived.restriction_isEquivalence

section

variable {R : Type u} [CommRing R] {A B : CochainDGAlgebra.{u, v} R}
variable (g : CochainDGAlgebra.Hom A B)

#synth (CochainDGAlgebra.Hom.Derived.extension g).Linear R
#synth (CochainDGAlgebra.Hom.Derived.extension g).CommShift ℤ
#synth (CochainDGAlgebra.Hom.Derived.extension g).IsTriangulated
#synth (CochainDGAlgebra.Hom.Derived.restriction g).Linear R
#synth (CochainDGAlgebra.Hom.Derived.restriction g).CommShift ℤ
#synth (CochainDGAlgebra.Hom.Derived.restriction g).IsTriangulated

end
