/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cech.Amitsur
public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily.Site
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Small

/-!
# Faithfully flat restriction maps for standard affine covers

This module records faithful flatness of the restriction homomorphism from an affine
covered object to the coproduct of a finite standard affine covering family.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite.Cech

noncomputable section

universe u

namespace AlgebraicGeometry.StandardTopology

/-- For a standard affine cover in any big standard topology, restriction from the covered
affine scheme to the coproduct of the covering schemes is faithfully flat. -/
theorem coproductSectionsMap_faithfullyFlat
    (τ : StandardTopology) (S : Scheme.{u}) (U : Over S) (n : ℕ)
    (𝒰 : Fin n → Over U)
    (h_affine : ∀ i, IsAffine ((Over.forget S).obj (𝒰 i).left))
    (h_cover : τ.IsCover
      (AffineFamilyOver.ofSiteFamily (Over.forget S) U n 𝒰 h_affine))
    [HasCoproduct (fun i ↦ (𝒰 i).left)] :
    RingHom.FaithfullyFlat
      (coproductSectionsMap ((Over.forget S).op ⋙ Scheme.Γ) U 𝒰) := sorry

end AlgebraicGeometry.StandardTopology

namespace AlgebraicGeometry.SmallStandardTopology

/-- For a standard affine cover on the small Zariski or small étale site, restriction from
the covered affine scheme to the coproduct of the covering schemes is faithfully flat. -/
theorem coproductSectionsMap_faithfullyFlat
    (σ : SmallStandardTopology) (S : Scheme.{u}) (U : σ.site S)
    (n : ℕ) (𝒰 : Fin n → Over U)
    (h_affine : ∀ i, IsAffine ((σ.toScheme S).obj (𝒰 i).left))
    (h_cover : σ.toStandard.IsCover
      (AffineFamilyOver.ofSiteFamily (σ.toScheme S) U n 𝒰 h_affine))
    [HasCoproduct (fun i ↦ (𝒰 i).left)] :
    RingHom.FaithfullyFlat
      (coproductSectionsMap ((σ.toScheme S).op ⋙ Scheme.Γ) U 𝒰) := sorry

end AlgebraicGeometry.SmallStandardTopology
