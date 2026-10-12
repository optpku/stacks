/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_21_5_TwoTerm
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape HomologicalComplex
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent
open AlgebraicGeometry.AlgebraicSpace.Modules
open scoped AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 76.21.5: if `f : X ⟶ Y` is locally of finite presentation, then `NL[X/Y]` is
étale locally on `X` quasi-isomorphic to a complex `… → 0 → F⁻¹ → F⁰ → 0 → …` of
quasi-coherent `𝒪_X`-modules with `F⁰` of finite presentation and `F⁻¹` of finite type. -/
@[stacks 0D0Z] #check
  (@AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent.exists_etaleLocal_twoTerm_of_locallyOfFinitePresentation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicSpace.LocallyOfFinitePresentation f],
      ∀ x : Points X, ∃ U : EtaleNeighborhood X x,
        ∃ (K : CochainComplex (ofOver U.toOver).Modules ℤ)
          (_ : K.IsStrictlyGE (-1)) (_ : K.IsStrictlyLE 0)
          (_ : (K.X (-1)).IsQuasicoherent) (_ : (K.X (-1)).IsFiniteType)
          (_ : (K.X 0).IsFinitePresentation),
          IsIsomorphic (DerivedCategory.Q.obj K)
            (DerivedCategory.Q.obj
              (((Modules.restrictFunctor U.toSite.hom).mapHomologicalComplex (up ℤ)).obj
                (naiveCotangent f))))
