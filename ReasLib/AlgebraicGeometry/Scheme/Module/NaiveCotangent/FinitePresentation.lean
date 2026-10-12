/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.AffineComparison.Derived
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape HomologicalComplex
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.NaiveCotangent

/-- For a locally finitely presented morphism of schemes, every point has an open
neighborhood on which the naive cotangent complex has a two-term representative whose
degree `-1` term is quasi-coherent and finite type and whose degree `0` term is finitely
presented. -/
@[stacks 0D0K]
theorem exists_local_twoTerm_of_locallyOfFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ (K : CochainComplex U.toScheme.Modules ℤ)
        (_ : K.IsStrictlyGE (-1)) (_ : K.IsStrictlyLE 0)
        (_ : (K.X (-1)).IsQuasicoherent) (_ : (K.X (-1)).IsFiniteType)
        (_ : (K.X 0).IsFinitePresentation),
        IsIsomorphic (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj
            (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (up ℤ)).obj
              (Scheme.Hom.naiveCotangent f))) := sorry

end AlgebraicGeometry.Scheme.Hom.NaiveCotangent
