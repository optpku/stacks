/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_83_4_Statements
public import stacks_project.Chap59.Theorem_59_82_7_Gabber_Restrict
public import stacks_project.Chap59.Lemma_59_80_9_Pullback
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Etale.TorsionOnCurve

/-- The constant sheaf of abelian groups on `X.smallEtaleTopology` with value
`ULift.{u} (ZMod ell)`. -/
public noncomputable abbrev constantZModSheaf (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}] (ell : ℕ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} (ZMod ell)))

/-- `constantZModSheaf` is `constantSheaf` applied to `AddCommGrpCat.of (ULift (ZMod ell))`. -/
public theorem constantZModSheaf_eq (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}] (ell : ℕ) :
    constantZModSheaf X ell =
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod ell))) := sorry

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
variable [Fact (topologicalKrullDim X.left ≤ 1)] [Smooth X.hom]
variable (ell : ℕ) [Fact (Nat.Prime ell)]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [Abelian (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasTerminal X.left.Etale]
variable [(siteAbelianSectionsFunctor X.left.smallEtaleTopology (terminal X.left.Etale)).Additive]

/-- The constant sheaf `ULift (ZMod ell)` is locally torsion on the small étale site. -/
public theorem constantZModSheaf_isLocallyTorsion :
    CategoryTheory.Sheaf.IsLocallyTorsion (constantZModSheaf X.left ell) := sorry

/-- Lemma 59.83.2 (1): étale cohomology of `constantZModSheaf X.left ell` vanishes in degrees
`q > 2`. -/
@[stacks 0A5B]
public theorem constantZMod_vanishing_gt_two
    {q : ℕ} (hq : 2 < q) :
    IsZero (etaleCohomology X.left (constantZModSheaf X.left ell) q) := sorry

/-- Lemma 59.83.2 (2): if `X` is affine, then étale cohomology of
`constantZModSheaf X.left ell` vanishes in degrees `q > 1`. -/
@[stacks 0A5B]
public theorem constantZMod_vanishing_of_isAffine
    (h_affine : IsAffine X.left) {q : ℕ} (hq : 1 < q) :
    IsZero (etaleCohomology X.left (constantZModSheaf X.left ell) q) := sorry

/-- Lemma 59.83.2 (3): if `constantZModSheaf X.left ell` is of `p`-power torsion and
`ringChar k = p`, then its étale cohomology vanishes in degrees `q > 1`. -/
@[stacks 0A5B]
public theorem constantZMod_vanishing_of_pPowerTorsion
    {p : ℕ} (hp : ringChar k = p)
    (hF : IsPPowerTorsion p (constantZModSheaf X.left ell)) {q : ℕ} (hq : 1 < q) :
    IsZero (etaleCohomology X.left (constantZModSheaf X.left ell) q) := sorry

/-- Lemma 59.83.2 (4): if `constantZModSheaf X.left ell` is constructible for étale inverse image
and `IsFiniteLocallyConstantAddCommGrp`, and of torsion prime to `ringChar k`, then each étale
cohomology group is finite. -/
@[stacks 0A5B]
public theorem constantZMod_finite_of_constructible_primeToChar
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
    (h_cons : IsConstructibleEtale (fun {Y} f ↦ (etaleAbelianRestriction f).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) (constantZModSheaf X.left ell))
    (h_prime : IsPrimeToCharTorsion k (constantZModSheaf X.left ell)) (q : ℕ) :
    Finite (etaleCohomology X.left (constantZModSheaf X.left ell) q) := sorry

/-- Lemma 59.83.2 (5): if `X` is proper over `k` and `constantZModSheaf X.left ell` is
constructible for étale inverse image and `IsFiniteLocallyConstantAddCommGrp`, then each étale
cohomology group is finite. -/
@[stacks 0A5B]
public theorem constantZMod_finite_of_isProper_constructible
    (h_proper : IsProper X.hom)
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
    (h_cons : IsConstructibleEtale (fun {Y} f ↦ (etaleAbelianRestriction f).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) (constantZModSheaf X.left ell))
    (q : ℕ) :
    Finite (etaleCohomology X.left (constantZModSheaf X.left ell) q) := sorry

/-- Lemma 59.83.2 (6): if `constantZModSheaf X.left ell` is of torsion prime to `ringChar k`,
then `etaleCohomologyRestrict` along the projection of a cartesian structure square
`X' = X ×_k k'` is an isomorphism in every degree. -/
@[stacks 0A5B]
public theorem constantZMod_baseChange_iso_primeToChar
    (h_prime : IsPrimeToCharTorsion k (constantZModSheaf X.left ell))
    {k' : Type u} [Field k'] [IsAlgClosed k'] [Algebra k k']
    (X' : SchemeOverField k') (π : X'.left ⟶ X.left)
    (h_baseChange : IsPullback π X'.hom X.hom (specMapOfAlgebra k'))
    [Scheme.Hom.FiniteType X'.hom] [IsSeparated X'.hom]
    [Abelian (Sheaf X'.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf X'.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal X'.left.Etale]
    [(siteAbelianSectionsFunctor X'.left.smallEtaleTopology (terminal X'.left.Etale)).Additive]
    [(etaleAbelianRestriction π).Additive]
    [(etaleAbelianRestriction π).PreservesHomology]
    [(etaleAbelianRestriction π).PreservesInjectiveObjects]
    [(etaleAbelianRestriction π ⋙
      siteAbelianSectionsFunctor X'.left.smallEtaleTopology (terminal X'.left.Etale)).Additive]
    (q : ℕ) :
    IsIso (etaleCohomologyRestrict π (constantZModSheaf X.left ell) q) := sorry

/-- Lemma 59.83.2 (7): if `X` is proper over `k`, then `etaleCohomologyRestrict` along the
projection of a cartesian structure square `X' = X ×_k k'` is an isomorphism in every degree. -/
@[stacks 0A5B]
public theorem constantZMod_baseChange_iso_of_isProper
    (h_proper : IsProper X.hom)
    {k' : Type u} [Field k'] [IsAlgClosed k'] [Algebra k k']
    (X' : SchemeOverField k') (π : X'.left ⟶ X.left)
    (h_baseChange : IsPullback π X'.hom X.hom (specMapOfAlgebra k'))
    [Scheme.Hom.FiniteType X'.hom] [IsSeparated X'.hom]
    [Abelian (Sheaf X'.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf X'.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal X'.left.Etale]
    [(siteAbelianSectionsFunctor X'.left.smallEtaleTopology (terminal X'.left.Etale)).Additive]
    [(etaleAbelianRestriction π).Additive]
    [(etaleAbelianRestriction π).PreservesHomology]
    [(etaleAbelianRestriction π).PreservesInjectiveObjects]
    [(etaleAbelianRestriction π ⋙
      siteAbelianSectionsFunctor X'.left.smallEtaleTopology (terminal X'.left.Etale)).Additive]
    (q : ℕ) :
    IsIso (etaleCohomologyRestrict π (constantZModSheaf X.left ell) q) := sorry

/-- Lemma 59.83.2 (8): for every open immersion `j : U ⟶ X`, `etaleCohomologyRestrict` in degree
`2` is an epimorphism. -/
@[stacks 0A5B]
public theorem constantZMod_h2_restrict_surjective
    {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j]
    [Abelian (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal U.Etale]
    [(siteAbelianSectionsFunctor U.smallEtaleTopology (terminal U.Etale)).Additive]
    [(etaleAbelianRestriction j).Additive]
    [(etaleAbelianRestriction j).PreservesHomology]
    [(etaleAbelianRestriction j).PreservesInjectiveObjects]
    [(etaleAbelianRestriction j ⋙
      siteAbelianSectionsFunctor U.smallEtaleTopology (terminal U.Etale)).Additive] :
    Epi (etaleCohomologyRestrict j (constantZModSheaf X.left ell) 2) := sorry

/-- If `finiteLocallyConstant` is `IsFiniteLocallyConstantAddCommGrp` and `pullbackH` agrees with
`etaleCohomologyRestrict` at morphisms where the latter is defined, then `StatementsHold` holds
for `constantZModSheaf X.left ell` at étale inverse image. -/
public theorem statementsHold_of_smooth_constantZMod
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
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
        etaleCohomology X.left (constantZModSheaf X.left ell) q ⟶
          etaleCohomology Y ((etaleAbelianRestriction f).obj (constantZModSheaf X.left ell)) q)
    (h_finite : ∀ (Y : Scheme.{u}) (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}),
      finiteLocallyConstant Y G ↔ IsFiniteLocallyConstantAddCommGrp G)
    (h_pullback :
      ∀ (Y : Scheme.{u}) (f : Y ⟶ X.left)
        [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
        [Abelian (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
        [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
        [HasTerminal Y.Etale]
        [(siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale)).Additive]
        [(etaleAbelianRestriction f).Additive]
        [(etaleAbelianRestriction f).PreservesHomology]
        [(etaleAbelianRestriction f).PreservesInjectiveObjects]
        [(etaleAbelianRestriction f ⋙
          siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale)).Additive]
        (q : ℕ),
        pullbackH Y f q = etaleCohomologyRestrict f (constantZModSheaf X.left ell) q) :
    StatementsHold X (constantZModSheaf X.left ell)
      (fun Y f ↦ (etaleAbelianRestriction f).obj) finiteLocallyConstant pullbackH := sorry


end AlgebraicGeometry.Etale.TorsionOnCurve
