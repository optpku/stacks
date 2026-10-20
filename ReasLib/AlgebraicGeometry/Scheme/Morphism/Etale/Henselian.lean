/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.Spec.IdealSubobject
public import ReasLib.RingTheory.Henselian.PairCriteria
import Mathlib.Tactic.CrossRefAttribute

/-!
# Étale morphisms over henselian pairs
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A quasi-compact separated étale scheme over a henselian pair decomposes into complementary
open subschemes, one finite over the base and one with empty special fibre. -/
@[stacks 0BTN "henselian étale decomposition"]
theorem exists_clopen_decomposition_of_henselianPair
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {U : Scheme.{u}} (f : U ⟶ Spec (CommRingCat.of A))
    [QuasiCompact f] [IsSeparated f] [Etale f]
    [IsFinite (pullback.snd f (Spec.quotientMap I))] :
    ∃ Ufin Uaway : U.Opens,
      IsCompl Ufin Uaway ∧ IsFinite (Ufin.ι ≫ f) ∧
        IsEmpty (pullback (Uaway.ι ≫ f) (Spec.quotientMap I) : Scheme) := sorry

/-- Two complementary-open decompositions of a quasi-compact separated étale scheme over a
henselian pair into a finite part and a part with empty special fibre agree componentwise. -/
theorem clopen_decomposition_unique_of_henselianPair
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {U : Scheme.{u}} (f : U ⟶ Spec (CommRingCat.of A))
    [QuasiCompact f] [IsSeparated f] [Etale f]
    [IsFinite (pullback.snd f (Spec.quotientMap I))]
    {Ufin Uaway Vfin Vaway : U.Opens}
    (hU : IsCompl Ufin Uaway ∧ IsFinite (Ufin.ι ≫ f) ∧
      IsEmpty (pullback (Uaway.ι ≫ f) (Spec.quotientMap I) : Scheme))
    (hV : IsCompl Vfin Vaway ∧ IsFinite (Vfin.ι ≫ f) ∧
      IsEmpty (pullback (Vaway.ι ≫ f) (Spec.quotientMap I) : Scheme)) :
    Ufin = Vfin ∧ Uaway = Vaway := sorry

end AlgebraicGeometry.Scheme.Hom
