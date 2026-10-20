module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory

universe u v w

variable {R : Type u} [CommRing R] (A : CochainDGAlgebra.{u, w} R)

/- Definition 22.22.2 (09KX): the derived category of `A` is the Verdier quotient of the
differential graded homotopy category by its acyclic objects. -/
@[stacks 09KX]
#check DifferentialGradedModule.Derived.Category.{u, v} A

/- The canonical quotient functor is a localization at quasi-isomorphisms. -/
#check DifferentialGradedModule.Derived.Q.{u, v} A

#check (inferInstance :
  (DifferentialGradedModule.Derived.Q.{u, v} A).IsLocalization
    (DifferentialGradedModule.quasiIso.{u, v} A))

/- Degree-zero homology descends canonically through the localization. -/
#check DifferentialGradedModule.Derived.homologyFunctor.{u, v} A 0

#check DifferentialGradedModule.Derived.homologyFunctorFactors.{u, v} A 0

#check DifferentialGradedModule.Derived.homologyFunctorUniqueIso.{u, v} A 0

#check DifferentialGradedModule.Derived.homologyFunctorUniqueIso_hom_app.{u, v} A 0
