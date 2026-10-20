/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective.Trace
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Trace

/-!
# Alternating traces of perfect complexes

The shared alternating cochain trace and the derived trace of a perfect
endomorphism both take values in `R♮`.
-/

universe u

open CategoryTheory HomologicalComplex
open scoped Ring

#check (CochainComplex.IsBoundedFiniteProjective.traceNatural :
    ∀ {R : Type u} [Ring R] {P : CochainComplex (ModuleCat R) ℤ}
    [P.IsBoundedFiniteProjective], (P ⟶ P) →+ R♮)

#check (CochainComplex.IsBoundedFiniteProjective.traceNatural_eq_sum :
    ∀ {R : Type u} [Ring R] {P : CochainComplex (ModuleCat R) ℤ}
    [P.IsBoundedFiniteProjective] (f : P ⟶ P) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b),
    CochainComplex.IsBoundedFiniteProjective.traceNatural f =
      ∑ i ∈ Finset.Icc a b,
        Int.negOnePow i •
          LinearMap.FiniteProjective.traceNatural (ModuleCat.Hom.hom (f.f i)))

#check (CochainComplex.IsBoundedFiniteProjective.traceNatural_homotopy :
    ∀ {R : Type u} [Ring R] {P : CochainComplex (ModuleCat R) ℤ}
    [P.IsBoundedFiniteProjective] {f g : P ⟶ P} (h_homotopy : Homotopy f g),
    CochainComplex.IsBoundedFiniteProjective.traceNatural f =
      CochainComplex.IsBoundedFiniteProjective.traceNatural g)

#check (CochainComplex.IsBoundedFiniteProjective.traceNatural_conjugate :
    ∀ {R : Type u} [Ring R] {P : CochainComplex (ModuleCat R) ℤ}
    [P.IsBoundedFiniteProjective] {Q : CochainComplex (ModuleCat R) ℤ}
    [Q.IsBoundedFiniteProjective] (γ1 : Q ⟶ P) (γ2 : P ⟶ Q)
    (h_homotopy : Homotopy (γ2 ≫ γ1) (𝟙 P)) (f : P ⟶ P),
    CochainComplex.IsBoundedFiniteProjective.traceNatural (γ1 ≫ f ≫ γ2) =
      CochainComplex.IsBoundedFiniteProjective.traceNatural f)

#check (DerivedCategory.IsPerfect.traceNatural :
    ∀ {R : Type u} [Ring R] {K : DerivedCategory (ModuleCat R)}
    (hK : DerivedCategory.IsPerfect K) (f : End K), R♮)
