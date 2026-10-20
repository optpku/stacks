/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve.Cohomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.IsExceptionalCurveFirstKind

/- Lemma 54.16.7 (1): let `E` be an exceptional curve of the first kind on a Noetherian
scheme `X`, and let the restriction of the invertible module `ℒ` to `E ≅ ℙ¹_k` be isomorphic to
`𝒪(n)`. If `H¹(X, ℒ) = 0` and `0 ≤ n`, then `H¹(X, ℒ(iE)) = 0` for every integer
`0 ≤ i ≤ n + 1`. -/
@[stacks 0C2J]
#check (AlgebraicGeometry.IsExceptionalCurveFirstKind.h1_isZero_twist_of_nonnegative_degree :
  ∀ {X : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (k : Type u) [Field k] (e : ProjectiveSpace.scheme k 1 ≅ E.subscheme) (n : ℤ)
    (hdegree : IsIsomorphic
      ((Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback E.subschemeι).obj ℒ))
      (ProjectiveSpace.twistingSheaf k 1 n))
    (hH1 : IsZero (RingedSpace.moduleCohomology ℒ 1)) (hn : 0 ≤ n),
    ∀ i : ℤ, 0 ≤ i → i ≤ n + 1 →
      IsZero (RingedSpace.moduleCohomology
        (Scheme.Modules.twistByTensorPower E.associatedSheaf ℒ i) 1))

/- Lemma 54.16.7 (2): in the same setting, if the restriction degree satisfies `n ≤ 0`,
then the canonical map `H¹(X, ℒ) ⟶ H¹(X, ℒ(E))` induced by the divisor section is injective. -/
@[stacks 0C2J]
#check (AlgebraicGeometry.IsExceptionalCurveFirstKind.h1_twistOneMap_injective_of_nonpositive_degree :
  ∀ {X : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (k : Type u) [Field k] (e : ProjectiveSpace.scheme k 1 ≅ E.subscheme) (n : ℤ)
    (hdegree : IsIsomorphic
      ((Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback E.subschemeι).obj ℒ))
      (ProjectiveSpace.twistingSheaf k 1 n))
    (hn : n ≤ 0),
    Function.Injective
      (RingedSpace.moduleCohomologyMap
        (RingedSpace.tensorSectionHom ℒ E.associatedSheaf E.canonicalSection) 1))

end AlgebraicGeometry.IsExceptionalCurveFirstKind
