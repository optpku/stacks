module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.NaiveCotangent

/-!
# Étale-local two-term models of the naive cotangent complex

A morphism of algebraic spaces that is locally of finite presentation has naive cotangent
complex étale-locally quasi-isomorphic to a two-term complex of quasi-coherent modules, with
finite type in degree `-1` and finite presentation in degree `0`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape HomologicalComplex
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Modules
open scoped AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent

/-- For a locally finitely presented morphism of algebraic spaces, every point of the source
has an étale neighbourhood on which the naive cotangent complex is quasi-isomorphic to a
two-term complex of quasi-coherent modules whose degree `-1` term is of finite type and
whose degree `0` term is of finite presentation. -/
theorem exists_etaleLocal_twoTerm_of_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.LocallyOfFinitePresentation f] :
    ∀ x : Points X, ∃ U : EtaleNeighborhood X x,
      ∃ (K : CochainComplex (ofOver U.toOver).Modules ℤ)
        (_ : K.IsStrictlyGE (-1)) (_ : K.IsStrictlyLE 0)
        (_ : (K.X (-1)).IsQuasicoherent) (_ : (K.X (-1)).IsFiniteType)
        (_ : (K.X 0).IsFinitePresentation),
        IsIsomorphic (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj
            (((Modules.restrictFunctor U.toSite.hom).mapHomologicalComplex (up ℤ)).obj
              (naiveCotangent f))) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent
