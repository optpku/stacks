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
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Etale.TorsionOnCurve

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
variable [Fact (topologicalKrullDim X.left ≤ 1)]
variable (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [Abelian (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasTerminal X.left.Etale]
variable [(siteAbelianSectionsFunctor X.left.smallEtaleTopology (terminal X.left.Etale)).Additive]

/-- Theorem 59.83.10 (1): étale cohomology of a locally torsion abelian sheaf `F` on `Xₑₜ`
vanishes in degrees `q > 2`. -/
@[stacks 03SC]
public theorem etaleCohomology_isZero_of_gt_two
    (hF : IsLocallyTorsion F) {q : ℕ} (hq : 2 < q) :
    IsZero (etaleCohomology X.left F q) := sorry

/-- Theorem 59.83.10 (2): if `X` is affine, then étale cohomology of a locally torsion abelian
sheaf `F` on `Xₑₜ` vanishes in degrees `q > 1`. -/
@[stacks 03SC]
public theorem etaleCohomology_isZero_of_isAffine
    (hF : IsLocallyTorsion F) (h_affine : IsAffine X.left) {q : ℕ} (hq : 1 < q) :
    IsZero (etaleCohomology X.left F q) := sorry

/-- Theorem 59.83.10 (3): if `p = ringChar k` is positive and a locally torsion abelian sheaf
`F` is of `p`-power torsion, then its étale cohomology vanishes in degrees `q > 1`. -/
@[stacks 03SC]
public theorem etaleCohomology_isZero_of_pPowerTorsion
    (hF : IsLocallyTorsion F) {p : ℕ} (hp_pos : 0 < p) (hp : ringChar k = p)
    (h_pow : IsPPowerTorsion p F) {q : ℕ} (hq : 1 < q) :
    IsZero (etaleCohomology X.left F q) := sorry

/-- Theorem 59.83.10 (4): if a locally torsion abelian sheaf `F` is constructible for étale
inverse image and `IsFiniteLocallyConstantAddCommGrp`, and of torsion prime to `ringChar k`,
then each étale cohomology group is finite. -/
@[stacks 03SC]
public theorem etaleCohomology_finite_of_constructible_primeToChar
    (hF : IsLocallyTorsion F)
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
    (h_cons : IsConstructibleEtale (fun {Y} f ↦ (etaleAbelianRestriction f).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F)
    (h_prime : IsPrimeToCharTorsion k F) (q : ℕ) :
    Finite (etaleCohomology X.left F q) := sorry

/-- Theorem 59.83.10 (5): if `X` is proper over `k` and a locally torsion abelian sheaf `F` is
constructible for étale inverse image and `IsFiniteLocallyConstantAddCommGrp`, then each étale
cohomology group is finite. -/
@[stacks 03SC]
public theorem etaleCohomology_finite_of_isProper_constructible
    (hF : IsLocallyTorsion F) (h_proper : IsProper X.hom)
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
    (h_cons : IsConstructibleEtale (fun {Y} f ↦ (etaleAbelianRestriction f).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F)
    (q : ℕ) :
    Finite (etaleCohomology X.left F q) := sorry

/-- Theorem 59.83.10 (6): if a locally torsion abelian sheaf `F` is of torsion prime to
`ringChar k`, then `etaleCohomologyRestrict` along the projection of a cartesian structure
square `X' = X ×_k k'` is an isomorphism in every degree. -/
@[stacks 03SC]
public theorem etaleCohomologyRestrict_isIso_of_primeToChar
    (hF : IsLocallyTorsion F) (h_prime : IsPrimeToCharTorsion k F)
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
    IsIso (etaleCohomologyRestrict π F q) := sorry

/-- Theorem 59.83.10 (7): if `X` is proper over `k`, then `etaleCohomologyRestrict` along the
projection of a cartesian structure square `X' = X ×_k k'` is an isomorphism in every degree. -/
@[stacks 03SC]
public theorem etaleCohomologyRestrict_isIso_of_isProper
    (hF : IsLocallyTorsion F) (h_proper : IsProper X.hom)
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
    IsIso (etaleCohomologyRestrict π F q) := sorry

/-- Theorem 59.83.10 (8): for every open immersion `j : U ⟶ X`, `etaleCohomologyRestrict` in
degree `2` is an epimorphism. -/
@[stacks 03SC]
public theorem etaleCohomologyRestrict_epi
    (hF : IsLocallyTorsion F) {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j]
    [Abelian (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal U.Etale]
    [(siteAbelianSectionsFunctor U.smallEtaleTopology (terminal U.Etale)).Additive]
    [(etaleAbelianRestriction j).Additive]
    [(etaleAbelianRestriction j).PreservesHomology]
    [(etaleAbelianRestriction j).PreservesInjectiveObjects]
    [(etaleAbelianRestriction j ⋙
      siteAbelianSectionsFunctor U.smallEtaleTopology (terminal U.Etale)).Additive] :
    Epi (etaleCohomologyRestrict j F 2) := sorry

/-- If `finiteLocallyConstant` is `IsFiniteLocallyConstantAddCommGrp` and `pullbackH` agrees with
`etaleCohomologyRestrict` at morphisms where the latter is defined, then `StatementsHold` holds
for a locally torsion abelian sheaf `F` at étale inverse image. -/
public theorem statementsHold_of_isLocallyTorsion
    (hF : IsLocallyTorsion F)
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
        etaleCohomology X.left F q ⟶
          etaleCohomology Y ((etaleAbelianRestriction f).obj F) q)
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
        pullbackH Y f q = etaleCohomologyRestrict f F q) :
    StatementsHold X F (fun Y f ↦ (etaleAbelianRestriction f).obj)
      finiteLocallyConstant pullbackH := sorry

end AlgebraicGeometry.Etale.TorsionOnCurve
