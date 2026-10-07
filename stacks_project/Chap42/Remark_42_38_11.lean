module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.TopChern

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators DirectSum

noncomputable section

universe u

/- Remark 42.38.11 (1): if only finitely many rank loci are nonempty, their top Chern
classes assemble as a finite sum in ordinary Chow cohomology. -/
@[stacks 0FA4] #check (AlgebraicGeometry.ChernClass.finiteTopChernClass_eq_sum :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (hfinite :
      {r : ℕ | (AlgebraicGeometry.Scheme.Modules.rankClopen E r : Set X).Nonempty}.Finite),
    AlgebraicGeometry.ChernClass.finiteTopChernClass δ π E hfinite =
      ∑ r ∈ hfinite.toFinset,
        DirectSum.of (AlgebraicGeometry.ChowCohomology.degree δ π) (r : ℤ)
          (AlgebraicGeometry.ChernClass.topDegreeOfRankComponents δ π E
            (fun s ↦ AlgebraicGeometry.ChernClass.rankComponent δ π E s
              ⟨s, Nat.lt_succ_self s⟩) r))

/- Remark 42.38.11 (2): without a finiteness assumption, the rankwise top Chern classes
assemble as a diagonal family in completed Chow cohomology. -/
@[stacks 0FA4] #check (AlgebraicGeometry.ChernClass.topChernClass_apply :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ),
    AlgebraicGeometry.ChernClass.topChernClass δ π E r =
      DirectSum.of (AlgebraicGeometry.ChernClass.RankComponentClass δ π E r) r
        (AlgebraicGeometry.ChernClass.rankComponent δ π E r
          ⟨r, Nat.lt_succ_self r⟩))
