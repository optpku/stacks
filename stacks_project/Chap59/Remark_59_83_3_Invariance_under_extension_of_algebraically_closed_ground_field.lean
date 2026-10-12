/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.RelativeRepresentability
public import stacks_project.Chap58.Theorem_58_6_2_InducedHom
public import stacks_project.Chap59.Lemma_59_83_2
public import stacks_project.Chap59.Remark_59_83_3_Invariance_under_extension_of_algebraically_closed_ground_field_ArtinSchreier

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Over.GlobalSections
open AlgebraicGeometry.Etale.TorsionOnCurve
open Polynomial
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Etale.AffineLine

/-- The affine line `A¹_R` over the spectrum of a commutative ring. -/
abbrev scheme (R : Type u) [CommRing R] : Scheme.{u} :=
  𝔸(ULift.{u} (Fin 1); Spec (CommRingCat.of R))

/-- `scheme R` is the underlying scheme of the relative affine line over `Spec R`. -/
theorem scheme_eq (R : Type u) [CommRing R] :
    scheme R = (affineLine (Spec (CommRingCat.of R))).left := sorry

/-- The morphism `A¹_{k'} ⟶ A¹_k` induced by a field extension `k → k'`. -/
def mapOfAlgebra (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    scheme k' ⟶ scheme k :=
  AffineSpace.map (ULift.{u} (Fin 1)) (specMapOfAlgebra k')

/-- `mapOfAlgebra` is `AffineSpace.map` of `specMapOfAlgebra`. -/
theorem mapOfAlgebra_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    mapOfAlgebra k k' =
      AffineSpace.map (ULift.{u} (Fin 1)) (specMapOfAlgebra k') := sorry

/-- Remark 59.83.3 (Invariance under extension of algebraically closed ground field) (1)
Let `k` be an algebraically closed field of characteristic `p > 0`. Then
étale cohomology `H¹(A¹_k, Z/pZ)` is isomorphic to the cokernel of the
Artin–Schreier operator `℘ : k[X] → k[X]`, `f ↦ f ^ p - f`, recovering the
exact sequence `k[X] ⟶ k[X] ⟶ H¹_étale(A¹_k, Z/pZ) ⟶ 0`. -/
@[stacks 0A47]
theorem h1_isIsomorphic_artinSchreierCoker
    (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    [HasSheafify (scheme k).smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf (scheme k).smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf (scheme k).smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal (scheme k).Etale]
    [(siteAbelianSectionsFunctor (scheme k).smallEtaleTopology
        (terminal (scheme k).Etale)).Additive] :
    IsIsomorphic
      (etaleCohomology (scheme k) (constantZModSheaf (scheme k) p) 1)
      (AddCommGrpCat.of (artinSchreierCoker p k)) := sorry

/-- Remark 59.83.3 (Invariance under extension of algebraically closed ground field) (2)
A set of representatives for the cokernel of `℘` is given by the polynomials
`∑_{p ∤ n} λ_n X ^ n` with `λ_n ∈ k`, i.e. the additive subgroup
`pCoprimeDegree p k`. (If `k` is not algebraically closed, extra constant
representatives are needed as well.) -/
@[stacks 0A47]
theorem pCoprimeDegree_represents_coker
    (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    Function.Bijective
      ((QuotientAddGroup.mk' (artinSchreier p k).range).comp
        (pCoprimeDegree p k).subtype) := sorry

/-- Remark 59.83.3 (Invariance under extension of algebraically closed ground field) (3)
If `k'/k` is an algebraically closed extension whose algebra map is not surjective,
then `H¹_étale(A¹_k, Z/pZ) ⟶ H¹_étale(A¹_{k'}, Z/pZ)` is not an isomorphism.
By Lemma 59.83.2 (6) this failure is special to `p`-power torsion in characteristic
`p`; it does not occur for torsion prime to the characteristic. -/
@[stacks 0A47]
theorem h1_baseChange_not_isIso
    (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    [Algebra k k'] (p : ℕ) [Fact p.Prime] [CharP k p]
    [HasSheafify (scheme k).smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf (scheme k).smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf (scheme k).smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal (scheme k).Etale]
    [(siteAbelianSectionsFunctor (scheme k).smallEtaleTopology
        (terminal (scheme k).Etale)).Additive]
    [HasSheafify (scheme k').smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf (scheme k').smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf (scheme k').smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal (scheme k').Etale]
    [(siteAbelianSectionsFunctor (scheme k').smallEtaleTopology
        (terminal (scheme k').Etale)).Additive]
    [((smallEtalePullback (mapOfAlgebra k k')).sheafPushforwardContinuous
        AddCommGrpCat.{u} (scheme k).smallEtaleTopology
        (scheme k').smallEtaleTopology).IsRightAdjoint]
    [(etaleAbelianRestriction (mapOfAlgebra k k')).Additive]
    [(etaleAbelianRestriction (mapOfAlgebra k k')).PreservesHomology]
    [(etaleAbelianRestriction (mapOfAlgebra k k')).PreservesInjectiveObjects]
    [(etaleAbelianRestriction (mapOfAlgebra k k') ⋙
        siteAbelianSectionsFunctor (scheme k').smallEtaleTopology
          (terminal (scheme k').Etale)).Additive]
    (h_ne : ¬ Function.Surjective (algebraMap k k')) :
    ¬ IsIso
        (etaleCohomologyRestrict (mapOfAlgebra k k')
          (constantZModSheaf (scheme k) p) 1) := sorry

/-- Remark 59.83.3 (Invariance under extension of algebraically closed ground field) (4)
In the same setting the induced map `π₁(A¹_{k'}) ⟶ π₁(A¹_k)` of étale fundamental
groups is not bijective. Thus the étale homotopy type of the affine line depends
on the algebraically closed ground field. -/
@[stacks 0A47]
theorem pi1_map_not_bijective
    (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    [Algebra k k'] (p : ℕ) [Fact p.Prime] [CharP k p]
    [ConnectedSpace (scheme k)] [ConnectedSpace (scheme k')]
    (xbar : GeometricPoint (scheme k'))
    (h_ne : ¬ Function.Surjective (algebraMap k k')) :
    ¬ Function.Bijective (etaleFundamentalGroupMap (mapOfAlgebra k k') xbar) := sorry

end AlgebraicGeometry.Etale.AffineLine
