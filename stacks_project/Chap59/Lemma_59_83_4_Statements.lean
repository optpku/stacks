/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Data.Finite.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Basic
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import stacks_project.Chap59.Definition_59_71_1_Constructible
public import stacks_project.Chap59.Proposition_59_54_2_Leray_spectral_sequence

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe u v w

namespace AlgebraicGeometry.Etale.TorsionOnCurve

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}

/-- A sheaf of abelian groups is of `p`-power torsion when every section is killed by a power of `p`. -/
public def IsPPowerTorsion (p : ℕ) (F : Sheaf J AddCommGrpCat.{u}) : Prop :=
  ∀ (U : C) (s : F.obj.obj (op U)), ∃ n : ℕ, (p ^ n : ℕ) • s = 0

/-- Unfolding of `p`-power torsion on sections. -/
public theorem isPPowerTorsion_iff (p : ℕ) (F : Sheaf J AddCommGrpCat.{u}) :
    IsPPowerTorsion p F ↔
      ∀ (U : C) (s : F.obj.obj (op U)), ∃ n : ℕ, (p ^ n : ℕ) • s = 0 := sorry

/-- A sheaf of abelian groups has torsion prime to the characteristic of `k` when every section is
killed by a positive integer coprime to `ringChar k`. -/
public def IsPrimeToCharTorsion (k : Type u) [Semiring k] (F : Sheaf J AddCommGrpCat.{u}) : Prop :=
  ∀ (U : C) (s : F.obj.obj (op U)),
    ∃ n : ℕ, n ≠ 0 ∧ n • s = 0 ∧ Nat.Coprime n (ringChar k)

/-- Unfolding of prime-to-characteristic torsion on sections. -/
public theorem isPrimeToCharTorsion_iff (k : Type u) [Semiring k] (F : Sheaf J AddCommGrpCat.{u}) :
    IsPrimeToCharTorsion k F ↔
      ∀ (U : C) (s : F.obj.obj (op U)),
        ∃ n : ℕ, n ≠ 0 ∧ n • s = 0 ∧ Nat.Coprime n (ringChar k) := sorry

/-- The morphism `Spec k' ⟶ Spec k` induced by a field extension `k → k'`. -/
public def specMapOfAlgebra {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k'] :
    Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k k'))

/-- Evaluation of `specMapOfAlgebra` is `Spec.map` of the ring map of the field extension. -/
public theorem specMapOfAlgebra_eq {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k'] :
    specMapOfAlgebra k' = Spec.map (CommRingCat.ofHom (algebraMap k k')) := sorry

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
variable [Fact (topologicalKrullDim X.left ≤ 1)]
variable (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [Abelian (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasTerminal X.left.Etale]
variable [(siteAbelianSectionsFunctor X.left.smallEtaleTopology (terminal X.left.Etale)).Additive]
variable (restrict :
    (Y : Scheme.{u}) → (Y ⟶ X.left) →
      Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u} →
        Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
variable (finiteLocallyConstant :
    (Y : Scheme.{u}) → Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} → Prop)
variable (pullbackH :
    (Y : Scheme.{u}) → (f : Y ⟶ X.left) →
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}] →
      [Abelian (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})] →
      [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})] →
      [HasTerminal Y.Etale] →
      [(siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale)).Additive] →
      (q : ℕ) →
      etaleCohomology X.left F q ⟶ etaleCohomology Y (restrict Y f F) q)

/-- Restriction of `H²` along an open immersion, as the degree-`2` component of `pullbackH`. -/
public def restrictH2AlongOpen
    {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j]
    [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal U.Etale]
    [(siteAbelianSectionsFunctor U.smallEtaleTopology (terminal U.Etale)).Additive] :
    etaleCohomology X.left F 2 ⟶ etaleCohomology U (restrict U j F) 2 :=
  pullbackH U j 2

/-- `restrictH2AlongOpen` is the degree-`2` component of the named cohomology pullback. -/
public theorem restrictH2AlongOpen_eq
    {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j]
    [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal U.Etale]
    [(siteAbelianSectionsFunctor U.smallEtaleTopology (terminal U.Etale)).Additive] :
    restrictH2AlongOpen X F restrict pullbackH j = pullbackH U j 2 := sorry

/-- The eight cohomology statements of Stacks Situation 59.83.1 that apply to a locally torsion
abelian sheaf `F` on a separated finite-type curve over an algebraically closed field. Clauses
(2)–(7) are implications from the extra hypotheses that make them applicable. Constructibility is
`IsConstructibleEtale` with the supplied restriction and finite-locally-constant data, matching
Definition 59.71.1 at the universe used by `etaleCohomology`. The family `pullbackH` is the named
étale cohomology comparison along a morphism, targeting `restrict f F`. For (6)(7) the morphism is
the projection of a cartesian structure square, so `X'` is a fiber product `X ×_k k'`. For (8) it is
an open immersion. -/
public class StatementsHold {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
    [Fact (topologicalKrullDim X.left ≤ 1)]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal X.left.Etale]
    [(siteAbelianSectionsFunctor X.left.smallEtaleTopology (terminal X.left.Etale)).Additive]
    (restrict :
      (Y : Scheme.{u}) → (Y ⟶ X.left) →
        Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u} →
          Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (finiteLocallyConstant :
      (Y : Scheme.{u}) → Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} → Prop)
    (pullbackH :
      (Y : Scheme.{u}) → (f : Y ⟶ X.left) →
        [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}] →
        [Abelian (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})] →
        [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})] →
        [HasTerminal Y.Etale] →
        [(siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale)).Additive] →
        (q : ℕ) →
        etaleCohomology X.left F q ⟶ etaleCohomology Y (restrict Y f F) q) : Prop where
  /-- The sheaf is locally torsion, as in Situation 59.83.1. -/
  isLocallyTorsion : CategoryTheory.Sheaf.IsLocallyTorsion F
  /-- (1): étale cohomology of `F` vanishes in degrees `q > 2`. -/
  vanishing_gt_two :
    ∀ q : ℕ, 2 < q → IsZero (etaleCohomology X.left F q)
  /-- (2): if `X` is affine, then étale cohomology of `F` vanishes in degrees `q > 1`. -/
  vanishing_of_isAffine :
    IsAffine X.left → ∀ q : ℕ, 1 < q → IsZero (etaleCohomology X.left F q)
  /-- (3): if `F` is of `p`-power torsion and `char k = p`, then étale cohomology of `F`
  vanishes in degrees `q > 1`. -/
  vanishing_of_pPowerTorsion :
    ∀ p : ℕ, ringChar k = p → IsPPowerTorsion p F →
      ∀ q : ℕ, 1 < q → IsZero (etaleCohomology X.left F q)
  /-- (4): if `F` is constructible and of torsion prime to `char k`, then each étale cohomology
  group of `F` is finite. -/
  finite_of_constructible_primeToChar :
    IsConstructibleEtale (fun {Y} f ↦ restrict Y f) (fun {Y} ↦ finiteLocallyConstant Y) F →
      IsPrimeToCharTorsion k F →
        ∀ q : ℕ, Finite (etaleCohomology X.left F q)
  /-- (5): if `X` is proper over `k` and `F` is constructible, then each étale cohomology group of
  `F` is finite. -/
  finite_of_isProper_constructible :
    IsProper X.hom →
      IsConstructibleEtale (fun {Y} f ↦ restrict Y f) (fun {Y} ↦ finiteLocallyConstant Y) F →
        ∀ q : ℕ, Finite (etaleCohomology X.left F q)
  /-- (6): if `F` is of torsion prime to `char k`, then named base-change maps
  `pullbackH π : H^q(X, F) ⟶ H^q(X_{k'}, F|_{X_{k'}})` are isomorphisms, for the projection
  of a cartesian structure square (so `X'` is a fiber product `X ×_k k'`). -/
  baseChange_iso_primeToChar :
    IsPrimeToCharTorsion k F →
      ∀ {k' : Type u} [Field k'] [IsAlgClosed k'] [Algebra k k']
        (X' : SchemeOverField k') (π : X'.left ⟶ X.left)
        (h_baseChange : IsPullback π X'.hom X.hom (specMapOfAlgebra k'))
        [Scheme.Hom.FiniteType X'.hom] [IsSeparated X'.hom]
        [HasSheafify X'.left.smallEtaleTopology AddCommGrpCat.{u}]
        [Abelian (Sheaf X'.left.smallEtaleTopology AddCommGrpCat.{u})]
        [HasInjectiveResolutions (Sheaf X'.left.smallEtaleTopology AddCommGrpCat.{u})]
        [HasTerminal X'.left.Etale]
        [(siteAbelianSectionsFunctor X'.left.smallEtaleTopology
            (terminal X'.left.Etale)).Additive]
        (q : ℕ),
        IsIso (pullbackH X'.left π q)
  /-- (7): if `X` is proper over `k`, then named base-change maps
  `pullbackH π : H^q(X, F) ⟶ H^q(X_{k'}, F|_{X_{k'}})` are isomorphisms, for the projection
  of a cartesian structure square (so `X'` is a fiber product `X ×_k k'`). -/
  baseChange_iso_of_isProper :
    IsProper X.hom →
      ∀ {k' : Type u} [Field k'] [IsAlgClosed k'] [Algebra k k']
        (X' : SchemeOverField k') (π : X'.left ⟶ X.left)
        (h_baseChange : IsPullback π X'.hom X.hom (specMapOfAlgebra k'))
        [Scheme.Hom.FiniteType X'.hom] [IsSeparated X'.hom]
        [HasSheafify X'.left.smallEtaleTopology AddCommGrpCat.{u}]
        [Abelian (Sheaf X'.left.smallEtaleTopology AddCommGrpCat.{u})]
        [HasInjectiveResolutions (Sheaf X'.left.smallEtaleTopology AddCommGrpCat.{u})]
        [HasTerminal X'.left.Etale]
        [(siteAbelianSectionsFunctor X'.left.smallEtaleTopology
            (terminal X'.left.Etale)).Additive]
        (q : ℕ),
        IsIso (pullbackH X'.left π q)
  /-- (8): restriction `H²(X, F) → H²(U, F|_U)` along an open immersion is an epimorphism. -/
  h2_restrict_surjective :
    ∀ {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j]
      [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
      [Abelian (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
      [HasInjectiveResolutions (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
      [HasTerminal U.Etale]
      [(siteAbelianSectionsFunctor U.smallEtaleTopology (terminal U.Etale)).Additive],
      Epi (restrictH2AlongOpen X F restrict pullbackH j)

/-- Assemble `StatementsHold` from its eight source clauses and the local-torsion hypothesis. -/
@[reducible]
public def StatementsHold.ofFields
    (isLocallyTorsion : CategoryTheory.Sheaf.IsLocallyTorsion F)
    (vanishing_gt_two :
      ∀ q : ℕ, 2 < q → IsZero (etaleCohomology X.left F q))
    (vanishing_of_isAffine :
      IsAffine X.left → ∀ q : ℕ, 1 < q → IsZero (etaleCohomology X.left F q))
    (vanishing_of_pPowerTorsion :
      ∀ p : ℕ, ringChar k = p → IsPPowerTorsion p F →
        ∀ q : ℕ, 1 < q → IsZero (etaleCohomology X.left F q))
    (finite_of_constructible_primeToChar :
      IsConstructibleEtale (fun {Y} f ↦ restrict Y f) (fun {Y} ↦ finiteLocallyConstant Y) F →
        IsPrimeToCharTorsion k F →
          ∀ q : ℕ, Finite (etaleCohomology X.left F q))
    (finite_of_isProper_constructible :
      IsProper X.hom →
        IsConstructibleEtale (fun {Y} f ↦ restrict Y f) (fun {Y} ↦ finiteLocallyConstant Y) F →
          ∀ q : ℕ, Finite (etaleCohomology X.left F q))
    (baseChange_iso_primeToChar :
      IsPrimeToCharTorsion k F →
        ∀ {k' : Type u} [Field k'] [IsAlgClosed k'] [Algebra k k']
          (X' : SchemeOverField k') (π : X'.left ⟶ X.left)
          (h_baseChange : IsPullback π X'.hom X.hom (specMapOfAlgebra k'))
          [Scheme.Hom.FiniteType X'.hom] [IsSeparated X'.hom]
          [HasSheafify X'.left.smallEtaleTopology AddCommGrpCat.{u}]
          [Abelian (Sheaf X'.left.smallEtaleTopology AddCommGrpCat.{u})]
          [HasInjectiveResolutions (Sheaf X'.left.smallEtaleTopology AddCommGrpCat.{u})]
          [HasTerminal X'.left.Etale]
          [(siteAbelianSectionsFunctor X'.left.smallEtaleTopology
              (terminal X'.left.Etale)).Additive]
          (q : ℕ),
          IsIso (pullbackH X'.left π q))
    (baseChange_iso_of_isProper :
      IsProper X.hom →
        ∀ {k' : Type u} [Field k'] [IsAlgClosed k'] [Algebra k k']
          (X' : SchemeOverField k') (π : X'.left ⟶ X.left)
          (h_baseChange : IsPullback π X'.hom X.hom (specMapOfAlgebra k'))
          [Scheme.Hom.FiniteType X'.hom] [IsSeparated X'.hom]
          [HasSheafify X'.left.smallEtaleTopology AddCommGrpCat.{u}]
          [Abelian (Sheaf X'.left.smallEtaleTopology AddCommGrpCat.{u})]
          [HasInjectiveResolutions (Sheaf X'.left.smallEtaleTopology AddCommGrpCat.{u})]
          [HasTerminal X'.left.Etale]
          [(siteAbelianSectionsFunctor X'.left.smallEtaleTopology
              (terminal X'.left.Etale)).Additive]
          (q : ℕ),
          IsIso (pullbackH X'.left π q))
    (h2_restrict_surjective :
      ∀ {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j]
        [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
        [Abelian (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
        [HasInjectiveResolutions (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
        [HasTerminal U.Etale]
        [(siteAbelianSectionsFunctor U.smallEtaleTopology (terminal U.Etale)).Additive],
        Epi (restrictH2AlongOpen X F restrict pullbackH j)) :
    StatementsHold X F restrict finiteLocallyConstant pullbackH :=
  { isLocallyTorsion := isLocallyTorsion
    vanishing_gt_two := vanishing_gt_two
    vanishing_of_isAffine := vanishing_of_isAffine
    vanishing_of_pPowerTorsion := vanishing_of_pPowerTorsion
    finite_of_constructible_primeToChar := finite_of_constructible_primeToChar
    finite_of_isProper_constructible := finite_of_isProper_constructible
    baseChange_iso_primeToChar := baseChange_iso_primeToChar
    baseChange_iso_of_isProper := baseChange_iso_of_isProper
    h2_restrict_surjective := h2_restrict_surjective }

/-- Projection of clause (1). -/
public theorem StatementsHold.vanishing_gt_two_apply
    [StatementsHold X F restrict finiteLocallyConstant pullbackH]
    {q : ℕ} (hq : 2 < q) :
    IsZero (etaleCohomology X.left F q) := sorry

/-- Projection of clause (2). -/
public theorem StatementsHold.vanishing_of_isAffine_apply
    [StatementsHold X F restrict finiteLocallyConstant pullbackH]
    (h_affine : IsAffine X.left) {q : ℕ} (hq : 1 < q) :
    IsZero (etaleCohomology X.left F q) := sorry

/-- Projection of clause (3). -/
public theorem StatementsHold.vanishing_of_pPowerTorsion_apply
    [StatementsHold X F restrict finiteLocallyConstant pullbackH]
    {p : ℕ} (hp : ringChar k = p) (hF : IsPPowerTorsion p F) {q : ℕ} (hq : 1 < q) :
    IsZero (etaleCohomology X.left F q) := sorry

/-- Projection of clause (4). -/
public theorem StatementsHold.finite_of_constructible_primeToChar_apply
    [StatementsHold X F restrict finiteLocallyConstant pullbackH]
    (h_cons : IsConstructibleEtale (fun {Y} f ↦ restrict Y f)
      (fun {Y} ↦ finiteLocallyConstant Y) F)
    (h_prime : IsPrimeToCharTorsion k F) (q : ℕ) :
    Finite (etaleCohomology X.left F q) := sorry

/-- Projection of clause (5). -/
public theorem StatementsHold.finite_of_isProper_constructible_apply
    [StatementsHold X F restrict finiteLocallyConstant pullbackH]
    (h_proper : IsProper X.hom)
    (h_cons : IsConstructibleEtale (fun {Y} f ↦ restrict Y f)
      (fun {Y} ↦ finiteLocallyConstant Y) F)
    (q : ℕ) :
    Finite (etaleCohomology X.left F q) := sorry

/-- Projection of clause (6) along a cartesian base-change projection. -/
public theorem StatementsHold.baseChange_iso_primeToChar_apply
    [StatementsHold X F restrict finiteLocallyConstant pullbackH]
    (h_prime : IsPrimeToCharTorsion k F)
    {k' : Type u} [Field k'] [IsAlgClosed k'] [Algebra k k']
    (X' : SchemeOverField k') (π : X'.left ⟶ X.left)
    (h_baseChange : IsPullback π X'.hom X.hom (specMapOfAlgebra k'))
    [Scheme.Hom.FiniteType X'.hom] [IsSeparated X'.hom]
    [HasSheafify X'.left.smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf X'.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf X'.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal X'.left.Etale]
    [(siteAbelianSectionsFunctor X'.left.smallEtaleTopology
        (terminal X'.left.Etale)).Additive]
    (q : ℕ) :
    IsIso (pullbackH X'.left π q) := sorry

/-- Projection of clause (7) along a cartesian base-change projection. -/
public theorem StatementsHold.baseChange_iso_of_isProper_apply
    [StatementsHold X F restrict finiteLocallyConstant pullbackH]
    (h_proper : IsProper X.hom)
    {k' : Type u} [Field k'] [IsAlgClosed k'] [Algebra k k']
    (X' : SchemeOverField k') (π : X'.left ⟶ X.left)
    (h_baseChange : IsPullback π X'.hom X.hom (specMapOfAlgebra k'))
    [Scheme.Hom.FiniteType X'.hom] [IsSeparated X'.hom]
    [HasSheafify X'.left.smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf X'.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf X'.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal X'.left.Etale]
    [(siteAbelianSectionsFunctor X'.left.smallEtaleTopology
        (terminal X'.left.Etale)).Additive]
    (q : ℕ) :
    IsIso (pullbackH X'.left π q) := sorry

/-- Projection of clause (8) as an epimorphism of the named open restriction on `H²`. -/
public theorem StatementsHold.h2_restrict_surjective_apply
    [StatementsHold X F restrict finiteLocallyConstant pullbackH]
    {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j]
    [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal U.Etale]
    [(siteAbelianSectionsFunctor U.smallEtaleTopology (terminal U.Etale)).Additive] :
    Epi (restrictH2AlongOpen X F restrict pullbackH j) := sorry

end AlgebraicGeometry.Etale.TorsionOnCurve
