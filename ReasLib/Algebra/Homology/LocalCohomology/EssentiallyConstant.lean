/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.LocalCohomology.MittagLeffler
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Diagram

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace localCohomology

/-- The cone induced by a map from a module to the inverse limit of a sequential system,
after applying local cohomology supported at the maximal ideal. -/
noncomputable def inverseSystemCone
    (A : Type u) [CommRing A] [IsLocalRing A] (M : ModuleCat.{u} A)
    (N : SequentialInverseSystem (FGModuleCat.{u} A))
    (f : M ⟶ limit (N ⋙ (ModuleCat.isFG A).ι)) (i : ℕ) :
    Cone (N ⋙ (ModuleCat.isFG A).ι ⋙
      localCohomology (IsLocalRing.maximalIdeal A) i) :=
  (localCohomology (IsLocalRing.maximalIdeal A) i).mapCone
    ((limit.cone (N ⋙ (ModuleCat.isFG A).ι)).extend f)

/-- The legs of `inverseSystemCone` are local cohomology applied to the composites of the
chosen map with the inverse-limit projections. -/
theorem inverseSystemCone_π_app
    (A : Type u) [CommRing A] [IsLocalRing A] (M : ModuleCat.{u} A)
    (N : SequentialInverseSystem (FGModuleCat.{u} A))
    (f : M ⟶ limit (N ⋙ (ModuleCat.isFG A).ι)) (i : ℕ) (n : ℕᵒᵖ) :
    (inverseSystemCone A M N f i).π.app n =
      (localCohomology (IsLocalRing.maximalIdeal A) i).map
        (f ≫ limit.π (N ⋙ (ModuleCat.isFG A).ι) n) := sorry

/-- The comparison morphism from the local cohomology of a module to the inverse limit of
the local cohomology of a sequential system. -/
noncomputable def limitComparison
    (A : Type u) [CommRing A] [IsLocalRing A] (M : ModuleCat.{u} A)
    (N : SequentialInverseSystem (FGModuleCat.{u} A))
    (f : M ⟶ limit (N ⋙ (ModuleCat.isFG A).ι)) (i : ℕ) :
    (localCohomology (IsLocalRing.maximalIdeal A) i).obj M ⟶
      limit (N ⋙ (ModuleCat.isFG A).ι ⋙
        localCohomology (IsLocalRing.maximalIdeal A) i) :=
  limit.lift _ (inverseSystemCone A M N f i)

/-- Composing `limitComparison` with a limit projection yields the corresponding leg of
`inverseSystemCone`. -/
theorem limitComparison_π
    (A : Type u) [CommRing A] [IsLocalRing A] (M : ModuleCat.{u} A)
    (N : SequentialInverseSystem (FGModuleCat.{u} A))
    (f : M ⟶ limit (N ⋙ (ModuleCat.isFG A).ι)) (i : ℕ) (n : ℕᵒᵖ) :
    limitComparison A M N f i ≫
        limit.π (N ⋙ (ModuleCat.isFG A).ι ⋙
          localCohomology (IsLocalRing.maximalIdeal A) i) n =
      (inverseSystemCone A M N f i).π.app n := sorry

/-- Under the finiteness and Noetherian hypotheses, an isomorphism comparison makes the
specified local-cohomology cone essentially constant. -/
theorem inverseSystemCone_isEssentiallyConstant
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (N : SequentialInverseSystem (FGModuleCat.{u} A))
    (f : M ⟶ limit (N ⋙ (ModuleCat.isFG A).ι)) (i : ℕ)
    [IsIso (limitComparison A M N f i)] :
    (inverseSystemCone A M N f i).IsEssentiallyConstant := sorry

/-- An isomorphism comparison makes the local-cohomology diagram essentially constant after
forgetting the specified cone vertex. -/
theorem isEssentiallyConstant_of_isIso_limitComparison
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (N : SequentialInverseSystem (FGModuleCat.{u} A))
    (f : M ⟶ limit (N ⋙ (ModuleCat.isFG A).ι)) (i : ℕ)
    [IsIso (limitComparison A M N f i)] :
    IsCofiltered.IsEssentiallyConstant
      (N ⋙ (ModuleCat.isFG A).ι ⋙
        localCohomology (IsLocalRing.maximalIdeal A) i) := sorry

end localCohomology
