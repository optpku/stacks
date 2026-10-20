/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.Map
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.RegularSection.Tensor
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.IsExceptionalCurveFirstKind

variable {X : Scheme.{u}} [IsNoetherian X]

/-- For an invertible module `ℒ` on a Noetherian scheme and an exceptional curve `E` of the
first kind, if `ℒ` restricts to `𝒪(n)` on a projective-line presentation of `E`, `0 ≤ n`, and
`H¹(X, ℒ) = 0`, then `H¹(X, ℒ(iE)) = 0` for every integer `0 ≤ i ≤ n + 1`. -/
theorem h1_isZero_twist_of_nonnegative_degree
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (k : Type u) [Field k] (e : ProjectiveSpace.scheme k 1 ≅ E.subscheme) (n : ℤ)
    (hdegree : IsIsomorphic
      ((Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback E.subschemeι).obj ℒ))
      (ProjectiveSpace.twistingSheaf k 1 n))
    (hH1 : IsZero (RingedSpace.moduleCohomology ℒ 1)) (hn : 0 ≤ n) :
    ∀ i : ℤ, 0 ≤ i → i ≤ n + 1 →
      IsZero (RingedSpace.moduleCohomology
        (Scheme.Modules.twistByTensorPower E.associatedSheaf ℒ i) 1) := sorry

/-- For an invertible module `ℒ` on a Noetherian scheme and an exceptional curve `E` of the
first kind, if `ℒ` restricts to `𝒪(n)` on a projective-line presentation of `E` and `n ≤ 0`,
then the divisor section induces an injective map `H¹(X, ℒ) ⟶ H¹(X, ℒ(E))`. -/
theorem h1_twistOneMap_injective_of_nonpositive_degree
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (k : Type u) [Field k] (e : ProjectiveSpace.scheme k 1 ≅ E.subscheme) (n : ℤ)
    (hdegree : IsIsomorphic
      ((Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback E.subschemeι).obj ℒ))
      (ProjectiveSpace.twistingSheaf k 1 n))
    (hn : n ≤ 0) :
    Function.Injective
      (RingedSpace.moduleCohomologyMap
        (RingedSpace.tensorSectionHom ℒ E.associatedSheaf E.canonicalSection) 1) := sorry

end AlgebraicGeometry.IsExceptionalCurveFirstKind
