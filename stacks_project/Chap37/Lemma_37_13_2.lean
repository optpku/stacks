/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.AffineComparison.Derived
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape HomologicalComplex
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 37.13.2: let `f : X ⟶ Y`, let `U ⊆ X` and `V ⊆ Y` be affine opens, and
assume `U ⊆ f⁻¹(V)`. The canonical comparison from the affine tilde of the algebraic
naive cotangent complex of `Γ(Y, V) ⟶ Γ(X, U)` to `NL[f.toShHom]` restricted to `U`
is an isomorphism in the derived category. -/
@[stacks 0D0I] #check
  (@AlgebraicGeometry.Scheme.Hom.NaiveCotangent.affineComparison_isIso :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
      (hU : IsAffineOpen U) [hV : Fact (IsAffineOpen V)] (e : U ≤ f ⁻¹ᵁ V),
      IsIso (DerivedCategory.Q.map
        (AlgebraicGeometry.Scheme.Hom.NaiveCotangent.affineComparison f hU e)))
