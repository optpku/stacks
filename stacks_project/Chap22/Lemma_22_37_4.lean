/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.DerivedMorita.Ordinary
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

variable {R : Type u} [CommRing R]
variable (A B : CochainDGAlgebra.{u, v} R)
variable (hA : A.IsConcentratedInDegreeZero)

/- Lemma 22.37.4 (1) (09S8): for a DGA concentrated in degree zero, derived Morita equivalence is
characterized by a compact generator with the prescribed shifted endomorphisms. -/
@[stacks 09S8] #check
  (CochainDGAlgebra.DerivedMorita.nonempty_equivalence_iff_exists_tilting
      A B hA :
    Nonempty (RLinear.TriangulatedEquivalence R
      (DifferentialGradedModule.Derived.Category.{u, v} A)
      (DifferentialGradedModule.Derived.Category.{u, v} B)) ↔
      ∃ P : DifferentialGradedModule.Derived.Category.{u, v} B,
        CochainDGAlgebra.DerivedMorita.IsTiltingFor A P)

#check @CochainDGAlgebra.DerivedMorita.IsTiltingFor
#check @CochainDGAlgebra.DerivedMorita.isTiltingFor_iff
#check @CochainDGAlgebra.DerivedMorita.isTiltingFor_iff_of_endEquiv
#check @CochainDGAlgebra.DerivedMorita.isTiltingFor_iff_regularEnd
#check @CochainDGAlgebra.DerivedMorita.IsTiltingFor.isSelfOrthogonal
#check @CategoryTheory.IsSelfOrthogonal
#check @CochainDGAlgebra.homologyZero
#check @CochainDGAlgebra.homologyZeroEquiv
#check @CochainDGAlgebra.Hom.homologyZeroMap
#check @DifferentialGradedModule.Derived.regularEndAlgHom
#check @DifferentialGradedModule.Derived.regularEndAlgHom_bijective
#check @DifferentialGradedModule.Derived.nonempty_homologyZeroAlgEquiv_regularEnd

/- Lemma 22.37.4 (2) (09S8): the constructed equivalence sends the regular object to the chosen
generator. -/
variable (P : DifferentialGradedModule.Derived.Category.{u, v} B)
variable (hP : CochainDGAlgebra.DerivedMorita.IsTiltingFor A P)

@[stacks 09S8] #check
  (CochainDGAlgebra.DerivedMorita.exists_equivalence_obj_regular A B hA P hP :
    ∃ e : RLinear.TriangulatedEquivalence R
        (DifferentialGradedModule.Derived.Category.{u, v} A)
        (DifferentialGradedModule.Derived.Category.{u, v} B),
      Nonempty (e.functor.obj (DifferentialGradedModule.Derived.regularObject A) ≅ P))
