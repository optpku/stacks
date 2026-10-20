module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.FinitePresentation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape HomologicalComplex
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 37.13.4: if `f : X ⟶ Y` is locally of finite presentation, then near every
point of `X`, the naive cotangent complex is represented by a complex supported in degrees
`-1` and `0`, whose degree `-1` term is quasi-coherent and finite type and whose degree `0`
term is finitely presented. -/
@[stacks 0D0K] #check
  (@AlgebraicGeometry.Scheme.Hom.NaiveCotangent.exists_local_twoTerm_of_locallyOfFinitePresentation :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f],
      ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
        ∃ (K : CochainComplex U.toScheme.Modules ℤ)
          (_ : K.IsStrictlyGE (-1)) (_ : K.IsStrictlyLE 0)
          (_ : (K.X (-1)).IsQuasicoherent) (_ : (K.X (-1)).IsFiniteType)
          (_ : (K.X 0).IsFinitePresentation),
          IsIsomorphic (DerivedCategory.Q.obj K)
            (DerivedCategory.Q.obj
              (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (up ℤ)).obj
                (Scheme.Hom.naiveCotangent f))))
