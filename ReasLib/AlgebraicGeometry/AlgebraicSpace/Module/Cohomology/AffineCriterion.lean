module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.VanishingH1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category

/-!
# Cohomological criteria for affineness of algebraic spaces

Affineness of a quasi-compact, absolutely quasi-separated algebraic space is
equivalent to vanishing of positive-degree cohomology of quasi-coherent modules.
Vanishing of first cohomology alone suffices.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact, absolutely quasi-separated algebraic space with vanishing
first cohomology for every quasi-coherent module is affine. -/
instance isAffine_of_hasVanishingH1 {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] : IsAffine X :=
  sorry

/-- A quasi-compact, absolutely quasi-separated algebraic space is affine if
and only if every quasi-coherent module has vanishing first cohomology. -/
theorem isAffine_iff_hasVanishingH1 {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})] :
    IsAffine X ↔ HasVanishingH1 X :=
  sorry

/-- For a quasi-compact, absolutely quasi-separated algebraic space with
vanishing first cohomology for every quasi-coherent module, the absolute
canonical morphism to the spectrum of its global sections is an isomorphism. -/
instance isIso_toSpecA_of_hasVanishingH1 {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] : IsIso (toSpecA X) :=
  sorry

/-- A quasi-compact, absolutely quasi-separated algebraic space is affine if
and only if every quasi-coherent module has vanishing cohomology in every
positive degree. -/
theorem isAffine_iff_cohomology_isZero {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})] :
    IsAffine X ↔ ∀ (F : Modules X), quasiCoherentModuleProperty X F →
      ∀ n : ℕ, 0 < n → CategoryTheory.Limits.IsZero (cohomology X F n) :=
  sorry

/-- On a Noetherian algebraic space, vanishing of first cohomology on every
coherent module implies vanishing of first cohomology on every quasi-coherent module. -/
theorem hasVanishingH1_of_coherent_h1_zero {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsNoetherian X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    (hH1 : ∀ (F : Modules X) [F.IsCoherent], CategoryTheory.Limits.IsZero (cohomology X F 1)) :
    HasVanishingH1 X :=
  sorry

/-- A Noetherian algebraic space with vanishing first cohomology for every
coherent module is represented by an affine scheme. -/
theorem isAffine_of_coherent_h1_zero {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsNoetherian X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    (hH1 : ∀ (F : Modules X) [F.IsCoherent], CategoryTheory.Limits.IsZero (cohomology X F 1)) :
    IsAffine X :=
  (isAffine_iff_hasVanishingH1 X).mpr (hasVanishingH1_of_coherent_h1_zero X hH1)

end AlgebraicGeometry.AlgebraicSpace
