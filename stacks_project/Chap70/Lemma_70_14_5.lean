/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SectionsWithSupport
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules

universe u

variable {S : Scheme.{u}} {X U : AlgebraicSpace S}

/- Lemma 70.14.5: on every étale chart, the supported subsheaf consists exactly of sections
whose support lies over the closed complement of the open subspace. -/
@[stacks 0859]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.range_sectionsWithSupportInι_app_eq_supportedSections :
  ∀ (ι : U ⟶ X) [IsOpenImmersion ι] (F : X.Modules) (W : smallEtaleSite X)
    {T : Set (Points X)}, T = (Set.range (Points.map ι))ᶜ →
      Set.range ((sectionsWithSupportInι ι F).val.app (op W)) =
        {s | sectionSupport F W s ⊆ Points.mapOfOver W.hom ⁻¹' T})

/- Lemma 70.14.5 (1): every affine étale chart admits a finitely generated ideal cutting out
the inverse image of the closed complement of a quasi-compact open subspace. -/
@[stacks 0859]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.exists_fg_ideal_of_quasiCompact_openComplement :
  ∀ (ι : U ⟶ X) [IsOpenImmersion ι] [QuasiCompact ι]
    {T : Set (Points X)}, IsClosed T → T = (Set.range (Points.map ι))ᶜ →
      ∀ (W : smallEtaleSite X) [IsAffine W.left.left],
        ∃ I : Ideal (structureRing W), I.FG ∧
          Points.mapOfOver W.hom ⁻¹' T =
            W.left.left.zeroLocus (I : Set (structureRing W)))

/- Lemma 70.14.5 (2): on an affine étale chart, the supported sections are precisely those
annihilated by a power of any finitely generated ideal cutting out the inverse image. -/
@[stacks 0859]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.range_sectionsWithSupportInι_app_eq_affine_idealPowerTorsion :
  ∀ (ι : U ⟶ X) [IsOpenImmersion ι] [QuasiCompact ι]
    (F : X.Modules) [F.IsQuasicoherent] {T : Set (Points X)},
      IsClosed T → T = (Set.range (Points.map ι))ᶜ →
        ∀ (W : smallEtaleSite X) [IsAffine W.left.left]
          (I : Ideal (structureRing W)), I.FG →
            Points.mapOfOver W.hom ⁻¹' T =
              W.left.left.zeroLocus (I : Set (structureRing W)) →
            Set.range ((sectionsWithSupportInι ι F).val.app (op W)) =
              {x | ∃ n : ℕ, ∀ a, a ∈ I ^ n → a • x = 0})

/- Lemma 70.14.5 (3): sections of a quasi-coherent module supported in the complement of a
quasi-compact open subspace form a quasi-coherent sheaf. -/
@[stacks 0859]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.sectionsWithSupportIn_isQuasicoherent :
  ∀ (ι : U ⟶ X) [IsOpenImmersion ι] [QuasiCompact ι]
    (F : X.Modules) [F.IsQuasicoherent], (sectionsWithSupportIn ι F).IsQuasicoherent)
