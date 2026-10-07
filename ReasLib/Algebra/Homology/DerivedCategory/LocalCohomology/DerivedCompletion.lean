module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Cech

/-!
# Local cohomology and derived completion

For a finitely generated ideal, this file records the canonical comparison maps between local
cohomology and derived completion, together with their naturality and invertibility.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology.Completion

variable {A : Type u} [CommRing A]

/-- The canonical map from the local cohomology of an object to the local cohomology of its
derived completion. -/
noncomputable def mapToDerivedCompletion (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ)
    (K : DerivedCategory (ModuleCat A)) :
    (RΓZ.obj K).obj ⟶
      (RΓZ.obj (DerivedCategory.derivedCompletionOf I hI K)).obj :=
  (IdealPowerTorsion.inclusion I).map
    (hRΓZ.homEquiv (RΓZ.obj K) (DerivedCategory.derivedCompletionOf I hI K)
      (hRΓZ.counit.app K ≫ DerivedCategory.toDerivedCompletion I hI K))

/-- The local-cohomology comparison with derived completion is the image of the universal
completion map under the ambient local-cohomology functor. -/
theorem mapToDerivedCompletion_eq_map (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ)
    (K : DerivedCategory (ModuleCat A)) :
    mapToDerivedCompletion I hI RΓZ hRΓZ K =
      (RΓZ ⋙ IdealPowerTorsion.inclusion I).map
        (DerivedCategory.toDerivedCompletion I hI K) := sorry

/-- The canonical map from local cohomology to local cohomology after derived completion is an
isomorphism. -/
noncomputable instance mapToDerivedCompletionIsIso (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ)
    (K : DerivedCategory (ModuleCat A)) :
    IsIso (mapToDerivedCompletion I hI RΓZ hRΓZ K) := sorry

/-- The map between derived completions induced by the local-cohomology counit. -/
noncomputable def derivedCompletionCounit (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ)
    (K : DerivedCategory (ModuleCat A)) :
    DerivedCategory.derivedCompletionOf I hI (RΓZ.obj K).obj ⟶
      DerivedCategory.derivedCompletionOf I hI K :=
  (DerivedCategory.derivedCompletion I hI).map (hRΓZ.counit.app K)

/-- The local-cohomology counit and its image under derived completion commute with the
universal maps to derived completion. -/
theorem derivedCompletionCounit_naturality (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ)
    (K : DerivedCategory (ModuleCat A)) :
    hRΓZ.counit.app K ≫ DerivedCategory.toDerivedCompletion I hI K =
      DerivedCategory.toDerivedCompletion I hI (RΓZ.obj K).obj ≫
        derivedCompletionCounit I hI RΓZ hRΓZ K := sorry

/-- The map between derived completions induced by the local-cohomology counit is an
isomorphism. -/
noncomputable instance derivedCompletionCounitIsIso (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ)
    (K : DerivedCategory (ModuleCat A)) :
    IsIso (derivedCompletionCounit I hI RΓZ hRΓZ K) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology.Completion
