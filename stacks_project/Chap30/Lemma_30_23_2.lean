/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Restriction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

/- Lemma 30.23.2 (1): for a Noetherian scheme `X` and ideal-sheaf data `I`, the
category of coherent formal modules along `I` is abelian. -/
@[stacks 087X] #check
  (AlgebraicGeometry.Scheme.coherentFormalModules_abelian :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData),
      Abelian (AlgebraicGeometry.Scheme.CoherentFormalModules X I))

/- Lemma 30.23.2 (2): restriction to an open subscheme gives an exact functor on
coherent formal modules. -/
@[stacks 087X] #check
  (AlgebraicGeometry.Scheme.coherentFormalModulesRestrictionFunctor_exact :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) (U : X.Opens),
      exactFunctor (AlgebraicGeometry.Scheme.CoherentFormalModules X I)
        (AlgebraicGeometry.Scheme.CoherentFormalModules (X.restrict U.isOpenEmbedding)
          (I.comap (X.ofRestrict U.isOpenEmbedding)))
        (AlgebraicGeometry.Scheme.coherentFormalModulesRestrictionFunctor I U))

/- Lemma 30.23.2 (3): exactness of a short complex of coherent formal modules can
be checked after restriction to every member of an open cover. -/
@[stacks 087X] #check
  (AlgebraicGeometry.Scheme.coherentFormalModules_exact_iff_of_openCover :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
      {ι : Type v} (U : ι → X.Opens) (_ : TopologicalSpace.IsOpenCover U)
      (S : ShortComplex (AlgebraicGeometry.Scheme.CoherentFormalModules X I)),
      S.Exact ↔
        ∀ i : ι,
          (S.map
            (AlgebraicGeometry.Scheme.coherentFormalModulesRestrictionFunctor I (U i))).Exact)
