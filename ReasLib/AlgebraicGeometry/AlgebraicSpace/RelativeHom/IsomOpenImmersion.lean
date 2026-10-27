/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.IsomFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.OpenImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-!
# Openness of the relative isomorphism functor

For proper finitely presented families, with flat source, invertible relative
morphisms form an open subfunctor of the relative morphism functor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Y B X : AlgebraicSpace S}

/-- For proper finitely presented families with flat source, a relative morphism
over a test scheme determines an open such that a test morphism factors through
this open precisely when the base-changed relative morphism is invertible. -/
theorem exists_opens_isIso_iff (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [FinitePresentation x] [Proper x]
    (σ : SchemeOver B) (b : (mor y x).obj (op σ)) :
    ∃ U : (σ.left.left).Opens,
      ∀ {τ : SchemeOver B} (h : τ ⟶ σ),
        Nonempty (Over.mk h.left.left ⟶ Over.mk U.ι) ↔
          IsIso (restrict y x h b) := sorry

/-- For proper finitely presented families with flat source, the inclusion of
the relative isomorphism functor into the relative morphism functor is an open
immersion. -/
theorem isOpenImmersion_isomι (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [FinitePresentation x] [Proper x] :
    Quot.IsOpenImmersionOnSchemesOver (isomSubfunctor y x).ι := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
