/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hilbert

/-!
# Example 108.4.10 (Coherent sheaves with fixed Hilbert polynomial)

Integer-valued rational Hilbert polynomials define open-and-closed algebraic
substacks. Their natural, disjoint clopen point loci cover every test scheme.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack
open CategoryTheory.MonoidalCategory
open scoped Bicategory

universe u

/- Example 108.4.10 (Coherent sheaves with fixed Hilbert polynomial): membership is equality at every integer and every point. -/
@[stacks 0DNF] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.mem_hilbert_iff :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (L : X.Modules) [isInvertibleObject L] (p : Polynomial ℚ)
    (hp : p.IsIntegerValued) (x : Obj f),
    hilbert f L hp.evalInt x ↔
      ∀ (n : ℤ) (t : Points (ofOver x.σ.left)),
        p.eval (n : ℚ) = (x.eulerChar (hilbertFamily L ⟨n⟩) t : ℚ))

/- The Hilbert inclusion is an open immersion. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.instOpenImmersion_ι_hilbert :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B)
    [FinitePresentation f] [Separated f] (L : X.Modules) [isInvertibleObject L]
    (P : ℤ → ℤ),
    CohStack.OpenImmersion (Hilbert.ι f L P))

section

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
  [FinitePresentation f] [Separated f] (L : X.Modules) [isInvertibleObject L]
  (P : ℤ → ℤ)

/- The Hilbert inclusion is a closed immersion. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical.instClosedImmersion
  f (hilbertFamily L) (fun n ↦ P n.down) (isPerfect_hilbertFamily L) :
  Hom.ClosedImmersion (Hilbert.ι f L P))

/- The Hilbert substack is algebraic. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical.instAlgebraicStack
  f (hilbertFamily L) (fun n ↦ P n.down) (isPerfect_hilbertFamily L) :
  AlgebraicStack (toGroupoidsHilbert f L P))

end

/- Each point has a unique polynomial agreeing at all integers. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.existsUnique_hilbertPolynomial :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (L : X.Modules) [isInvertibleObject L] (x : Obj f)
    (t : Points (ofOver x.σ.left)),
    ∃! p : Polynomial ℚ, p.IsIntegerValued ∧
      ∀ n : ℤ, p.eval (n : ℚ) = (x.eulerChar (hilbertFamily L ⟨n⟩) t : ℚ))

/- Whole-family uniqueness holds when the test scheme has a point. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.eq_of_mem_hilbert :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (L : X.Modules) [isInvertibleObject L] (p q : Polynomial ℚ)
    (hp : p.IsIntegerValued) (hq : q.IsIntegerValued) (x : Obj f)
    (hT : Nonempty (Points (ofOver x.σ.left))) (hxp : hilbert f L hp.evalInt x)
    (hxq : hilbert f L hq.evalInt x),
    p = q)

/- A connected test scheme has a global Hilbert polynomial. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.exists_mem_hilbert_of_isConnected :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (L : X.Modules) [isInvertibleObject L] (x : Obj f)
    [ConnectedSpace x.σ.left.left],
    ∃ p : Polynomial ℚ, ∃ hp : p.IsIntegerValued, hilbert f L hp.evalInt x)

/- Whole-space loci characterize substack membership. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Obj.hilbertLocus_eq_univ_iff :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    {f : X ⟶ B} [FinitePresentation f]
    (x : Obj f) (L : X.Modules) [isInvertibleObject L] (P : ℤ → ℤ),
    x.hilbertLocus L P = Set.univ ↔ hilbert f L P x)

/- The point loci are open and closed. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Obj.isClopen_hilbertLocus :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    {f : X ⟶ B} [FinitePresentation f] [Separated f]
    (x : Obj f) (L : X.Modules) [isInvertibleObject L] (P : ℤ → ℤ),
    IsClopen (x.hilbertLocus L P))

/- The point loci are natural under coherent-family morphisms. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Obj.hilbertLocus_natural :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    {f : X ⟶ B} [FinitePresentation f]
    {x y : Obj f} (α : Hom x y) (L : X.Modules) [isInvertibleObject L]
    (P : ℤ → ℤ),
    x.hilbertLocus L P =
      Points.map (ofOverMap α.base.left) ⁻¹' y.hilbertLocus L P)

/- Distinct polynomial loci are disjoint. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Obj.hilbertLocus_pairwiseDisjoint :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    {f : X ⟶ B} [FinitePresentation f]
    (x : Obj f) (L : X.Modules) [isInvertibleObject L],
    Pairwise (fun p q : {p : Polynomial ℚ // p.IsIntegerValued} ↦
      Disjoint (x.hilbertLocus L p.property.evalInt)
        (x.hilbertLocus L q.property.evalInt)))

/- The polynomial loci cover every test scheme. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Obj.iUnion_hilbertLocus :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    {f : X ⟶ B} [FinitePresentation f] [Separated f]
    (x : Obj f) (L : X.Modules) [isInvertibleObject L],
    (⋃ p : {p : Polynomial ℚ // p.IsIntegerValued},
      x.hilbertLocus L p.property.evalInt) = Set.univ)

