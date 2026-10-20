/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Cohomology
public import ReasLib.CategoryTheory.Preadditive.HomCongr
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived Hom from K-Projective and K-Injective Resolutions

This leaf packages the canonical Hom-set equivalences obtained by combining the
homotopy-to-derived localization with a quasi-isomorphic K-projective source or K-injective
target. It is independent of any particular construction of resolutions.
-/

open CategoryTheory ComplexShape DerivedCategory HomotopyCategory

noncomputable section

universe r w v u

namespace CochainComplex.Resolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Lemma 22.22.3 (1): a quasi-isomorphic K-projective source computes morphisms in the derived
category. -/
@[stacks 09KY]
noncomputable def projectiveHomEquiv
    (P M N : CochainComplex C ℤ) (q : P ⟶ M) [P.IsKProjective]
    [IsIso (DerivedCategory.Q.map q)] :
    ((HomotopyCategory.quotient C (up ℤ)).obj P ⟶
        (HomotopyCategory.quotient C (up ℤ)).obj N) ≃
      (DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj N) :=
  (Equiv.ofBijective
      (DerivedCategory.Qh.map :
        ((HomotopyCategory.quotient C (up ℤ)).obj P ⟶
            (HomotopyCategory.quotient C (up ℤ)).obj N) →
          (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj N))
      (IsKProjective.Qh_map_bijective P
        ((HomotopyCategory.quotient C (up ℤ)).obj N))).trans
    (Iso.homCongr
      (asIso (DerivedCategory.Q.map q) :
        DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj M)
      (Iso.refl _))

/-- The canonical projective-resolution Hom equivalence is linear in every compatible
enrichment ring. -/
theorem projectiveHomEquiv_isLinearMap
    (R : Type r) [Ring R] [Linear R C]
    (P M N : CochainComplex C ℤ) (q : P ⟶ M) [P.IsKProjective]
    [IsIso (DerivedCategory.Q.map q)] :
    IsLinearMap R (projectiveHomEquiv P M N q) := sorry

/-- The linear equivalence from maps out of a K-projective resolution in the homotopy category
to maps from the resolved object in the derived category. -/
noncomputable def projectiveHomLinearEquiv
    (R : Type r) [Ring R] [Linear R C]
    (P M N : CochainComplex C ℤ) (q : P ⟶ M) [P.IsKProjective]
    [IsIso (DerivedCategory.Q.map q)] :
    ((HomotopyCategory.quotient C (up ℤ)).obj P ⟶
        (HomotopyCategory.quotient C (up ℤ)).obj N) ≃ₗ[R]
      (DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj N) :=
  (projectiveHomEquiv P M N q).toLinearEquiv
    (projectiveHomEquiv_isLinearMap R P M N q)

/-- Evaluation of `projectiveHomEquiv`: localize the homotopy-class morphism and precompose with
the inverse of the resolution quasi-isomorphism. -/
@[simp]
theorem projectiveHomEquiv_apply
    (P M N : CochainComplex C ℤ) (q : P ⟶ M) [P.IsKProjective]
    [IsIso (DerivedCategory.Q.map q)]
    (f : (HomotopyCategory.quotient C (up ℤ)).obj P ⟶
      (HomotopyCategory.quotient C (up ℤ)).obj N) :
    projectiveHomEquiv P M N q f =
      (asIso (DerivedCategory.Q.map q)).inv ≫ DerivedCategory.Qh.map f := sorry

/-- Lemma 22.22.3 (2): a quasi-isomorphic K-injective target computes morphisms in the derived
category. -/
@[stacks 09KY]
noncomputable def injectiveHomEquiv
    (M N I : CochainComplex C ℤ) (i : N ⟶ I) [I.IsKInjective]
    [IsIso (DerivedCategory.Q.map i)] :
    ((HomotopyCategory.quotient C (up ℤ)).obj M ⟶
        (HomotopyCategory.quotient C (up ℤ)).obj I) ≃
      (DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj N) :=
  (Equiv.ofBijective
      (DerivedCategory.Qh.map :
        ((HomotopyCategory.quotient C (up ℤ)).obj M ⟶
            (HomotopyCategory.quotient C (up ℤ)).obj I) →
          (DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj I))
      (IsKInjective.Qh_map_bijective
        ((HomotopyCategory.quotient C (up ℤ)).obj M) I)).trans
    (Iso.homCongr (Iso.refl _) (asIso (DerivedCategory.Q.map i)).symm)

/-- The canonical injective-resolution Hom equivalence is linear in every compatible
enrichment ring. -/
theorem injectiveHomEquiv_isLinearMap
    (R : Type r) [Ring R] [Linear R C]
    (M N I : CochainComplex C ℤ) (i : N ⟶ I) [I.IsKInjective]
    [IsIso (DerivedCategory.Q.map i)] :
    IsLinearMap R (injectiveHomEquiv M N I i) := sorry

/-- The linear equivalence from maps into a K-injective resolution in the homotopy category
to maps into the resolved object in the derived category. -/
noncomputable def injectiveHomLinearEquiv
    (R : Type r) [Ring R] [Linear R C]
    (M N I : CochainComplex C ℤ) (i : N ⟶ I) [I.IsKInjective]
    [IsIso (DerivedCategory.Q.map i)] :
    ((HomotopyCategory.quotient C (up ℤ)).obj M ⟶
        (HomotopyCategory.quotient C (up ℤ)).obj I) ≃ₗ[R]
      (DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj N) :=
  (injectiveHomEquiv M N I i).toLinearEquiv
    (injectiveHomEquiv_isLinearMap R M N I i)

/-- Evaluation of `injectiveHomEquiv`: localize the homotopy-class morphism and postcompose with
the inverse of the resolution quasi-isomorphism. -/
@[simp]
theorem injectiveHomEquiv_apply
    (M N I : CochainComplex C ℤ) (i : N ⟶ I) [I.IsKInjective]
    [IsIso (DerivedCategory.Q.map i)]
    (f : (HomotopyCategory.quotient C (up ℤ)).obj M ⟶
      (HomotopyCategory.quotient C (up ℤ)).obj I) :
    injectiveHomEquiv M N I i f =
      DerivedCategory.Qh.map f ≫ (asIso (DerivedCategory.Q.map i)).inv := sorry

/-- Lemma 22.31.4 (0CS5): if `i : M ⟶ I` is a K-injective resolution, degree-`n`
Hom-complex cohomology is canonically the `R`-module of derived morphisms from `K` to
`M⟦n⟧`. -/
@[stacks 0CS5 "Hom-complex cohomology as derived shifted Hom"]
noncomputable def injectiveHomologyLinearEquiv
    (R : Type r) [Ring R] [Linear R C]
    (K M I : CochainComplex C ℤ) (i : M ⟶ I) [I.IsKInjective]
    [IsIso (DerivedCategory.Q.map i)] (n : ℤ) :
    (CochainComplex.HomComplex.homologyModule R K I n : Type v) ≃ₗ[R]
      (DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj M)⟦n⟧) :=
  (CochainComplex.HomComplex.homologyHomLinearEquiv R K I n).trans
    ((injectiveHomLinearEquiv R K (I⟦n⟧) (I⟦n⟧) (𝟙 _)).trans
      ((CategoryTheory.Linear.homCongr R (Iso.refl _)
          ((DerivedCategory.Q.commShiftIso n).app I)).trans
      (CategoryTheory.Linear.homCongr R (Iso.refl _)
          (asIso ((DerivedCategory.Q.map i)⟦n⟧')).symm)))

/-- The degree-`n` additive Hom-complex equivalence for a K-injective target. -/
@[stacks 0CS5 "degree-n K-injective Hom-complex additive equivalence"]
noncomputable def injectiveHomologyAddEquiv
    (L I : CochainComplex C ℤ) [I.IsKInjective] (n : ℤ) :
    (CochainComplex.HomComplex L I).homology n ≃+
      ((DerivedCategory.Q.obj L : DerivedCategory C) ⟶
        (DerivedCategory.Q.obj I)⟦n⟧) :=
  let KQ := HomotopyCategory.quotient C (up ℤ)
  let e₀ :
      (CochainComplex.HomComplex L I).homology n ≃+
        (KQ.obj L ⟶ KQ.obj (I⟦n⟧)) :=
    CochainComplex.HomComplex.homologyHomAddEquiv L I n
  let e₁ : (KQ.obj L ⟶ KQ.obj (I⟦n⟧)) ≃+
      (DerivedCategory.Qh.obj (KQ.obj L) ⟶
        DerivedCategory.Qh.obj (KQ.obj (I⟦n⟧))) :=
    AddEquiv.ofBijective
      (DerivedCategory.Qh.mapAddHom :
        (KQ.obj L ⟶ KQ.obj (I⟦n⟧)) →+
          (DerivedCategory.Qh.obj (KQ.obj L) ⟶
            DerivedCategory.Qh.obj (KQ.obj (I⟦n⟧))))
      (CochainComplex.IsKInjective.Qh_map_bijective (KQ.obj L) (I⟦n⟧))
  let e₂ :
      (DerivedCategory.Qh.obj (KQ.obj L) ⟶
          DerivedCategory.Qh.obj (KQ.obj (I⟦n⟧))) ≃+
        ((DerivedCategory.Q.obj L : DerivedCategory C) ⟶
          (DerivedCategory.Q.obj I)⟦n⟧) :=
    (Iso.homCongrAddEquiv ((quotientCompQhIso C).app L)
      ((quotientCompQhIso C).app (I⟦n⟧))).trans
      (Iso.homCongrAddEquiv (Iso.refl _)
        ((DerivedCategory.Q.commShiftIso n).app I))
  e₀.trans (e₁.trans e₂)

/-- The degree-zero additive Hom-complex equivalence for a K-injective target.  This is the
unshifted specialization of `injectiveHomologyAddEquiv`, exposed at the additive-group level used
by ordinary derived-Hom statements. -/
@[stacks 0A94 "degree-zero K-injective Hom-complex equivalence"]
noncomputable def injectiveHomologyZeroAddEquiv
    (L I : CochainComplex C ℤ) [I.IsKInjective] :
    (CochainComplex.HomComplex L I).homology (0 : ℤ) ≃+
      ((DerivedCategory.Q.obj L : DerivedCategory C) ⟶
        (DerivedCategory.Q.obj I : DerivedCategory C)) :=
  (injectiveHomologyAddEquiv L I 0).trans
    (Iso.homCongrAddEquiv (Iso.refl _)
      ((shiftFunctorZero (DerivedCategory C) ℤ).app (DerivedCategory.Q.obj I)))

/-- Transport the degree-`n` K-injective Hom-complex equivalence across chosen derived-category
representations of its source and target. -/
@[stacks 0CS5 "degree-n K-injective Hom equivalence for represented objects"]
noncomputable def injectiveHomologyAddEquivOfIso
    (L I : CochainComplex C ℤ) [I.IsKInjective]
    {K M : DerivedCategory C}
    (eL : DerivedCategory.Q.obj L ≅ K)
    (eI : DerivedCategory.Q.obj I ≅ M) (n : ℤ) :
    (CochainComplex.HomComplex L I).homology n ≃+
      (K ⟶ M⟦n⟧) :=
  (injectiveHomologyAddEquiv L I n).trans
    (Iso.homCongrAddEquiv eL
      (asIso (eI.hom⟦n⟧')))

/-- Transport the degree-zero K-injective Hom-complex equivalence across chosen
derived-category representations. -/
@[stacks 0A94 "K-injective Hom equivalence for represented objects"]
noncomputable def injectiveHomologyZeroAddEquivOfIso
    (L I : CochainComplex C ℤ) [I.IsKInjective]
    {K M : DerivedCategory C}
    (eL : DerivedCategory.Q.obj L ≅ K)
    (eI : DerivedCategory.Q.obj I ≅ M) :
    (CochainComplex.HomComplex L I).homology (0 : ℤ) ≃+
      (K ⟶ M) :=
  (injectiveHomologyZeroAddEquiv L I).trans
    (Iso.homCongrAddEquiv eL eI)

/- The additive equivalence is the primary downstream surface.  Keep its two variablewise
naturalities explicit so clients do not need to unfold the localization composite. -/
/-- The K-injective Hom-cohomology equivalence is contravariantly natural in its source. -/
@[stacks 0CS5 "additive Hom-complex naturality in the source"]
theorem injectiveHomologyAddEquiv_naturality_left
    {L L' I : CochainComplex C ℤ} (f : L ⟶ L') [I.IsKInjective] (n : ℤ)
    (x : (CochainComplex.HomComplex L' I).homology n) :
    injectiveHomologyAddEquiv L I n
        (HomologicalComplex.homologyMap
          (CategoryTheory.CochainComplex.homComplexPrecomp (f := f) (I := I)) n x) =
      DerivedCategory.Q.map f ≫ injectiveHomologyAddEquiv L' I n x := sorry

/-- The K-injective Hom-cohomology equivalence is covariantly natural in its target complex. -/
@[stacks 0CS5 "additive Hom-complex naturality in the target"]
theorem injectiveHomologyAddEquiv_naturality_right
    {L I I' : CochainComplex C ℤ} (g : I ⟶ I') [I.IsKInjective] [I'.IsKInjective]
    (n : ℤ) (x : (CochainComplex.HomComplex L I).homology n) :
    injectiveHomologyAddEquiv L I' n
        (HomologicalComplex.homologyMap
          (CategoryTheory.CochainComplex.homComplexPostcomp (N := L) g) n x) =
      injectiveHomologyAddEquiv L I n x ≫ (DerivedCategory.Q.map g)⟦n⟧' := sorry

/-- The K-injective Hom-cohomology equivalence is contravariantly natural in its source
complex. -/
theorem injectiveHomologyLinearEquiv_naturality_left
    (R : Type r) [Ring R] [Linear R C]
    {K K' M I : CochainComplex C ℤ} (f : K ⟶ K') (i : M ⟶ I)
    [I.IsKInjective] [IsIso (DerivedCategory.Q.map i)] (n : ℤ)
    (x : (CochainComplex.HomComplex K' I).homology n) :
    injectiveHomologyLinearEquiv R K M I i n
        (HomologicalComplex.homologyMap
          (CategoryTheory.CochainComplex.homComplexPrecomp (f := f) (I := I)) n x) =
      DerivedCategory.Q.map f ≫
        injectiveHomologyLinearEquiv R K' M I i n x := sorry

/-- The K-injective Hom-cohomology equivalence is covariantly natural in a morphism of resolved
targets and a compatible morphism between their K-injective resolutions. -/
theorem injectiveHomologyLinearEquiv_naturality_right
    (R : Type r) [Ring R] [Linear R C]
    {K M M' I I' : CochainComplex C ℤ} (i : M ⟶ I) (i' : M' ⟶ I')
    [I.IsKInjective] [I'.IsKInjective]
    [IsIso (DerivedCategory.Q.map i)] [IsIso (DerivedCategory.Q.map i')]
    (f : M ⟶ M') (g : I ⟶ I') (comm : i ≫ g = f ≫ i') (n : ℤ)
    (x : (CochainComplex.HomComplex K I).homology n) :
    injectiveHomologyLinearEquiv R K M' I' i' n
        (HomologicalComplex.homologyMap
          (CategoryTheory.CochainComplex.homComplexPostcomp (N := K) g) n x) =
      injectiveHomologyLinearEquiv R K M I i n x ≫
        (DerivedCategory.Q.map f)⟦n⟧' := sorry

end CochainComplex.Resolution
