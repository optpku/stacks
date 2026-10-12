/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed

/-!
# Injective resolutions on canonical small scheme sites

This module records canonical injective-resolution facts and explicit higher
direct images for module sheaves on the small Zariski and small étale sites.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Zariski.Small

/-- Module sheaves on the small Zariski site admit injective resolutions in the
carrier universe used by ringed-site derived images. -/
theorem moduleCatHasInjectiveResolutions (S : Scheme.{u}) :
    HasInjectiveResolutions
      (RingedSite.ModuleCat.{u + 1} (ringedSite S)) := sorry

/-- The degree-`i` higher direct image of a module sheaf along the small
Zariski-site morphism induced by a scheme morphism. -/
noncomputable def higherDirectImageModule {S T : Scheme.{u}} (f : T ⟶ S)
    (ℱ : RingedSite.ModuleCat.{u + 1} (ringedSite T)) (i : ℕ) :
    RingedSite.ModuleCat.{u + 1} (ringedSite S) :=
  @RingedSite.Hom.higherDirectImageModule
    (ringedSite T) (ringedSite S) (ringedHom f)
    inferInstance inferInstance (moduleCatHasInjectiveResolutions T) ℱ i

end AlgebraicGeometry.Scheme.Zariski.Small

namespace AlgebraicGeometry.Scheme.Etale.Small

/-- Module sheaves on the small étale site admit injective resolutions in the
carrier universe used by ringed-site derived images. -/
theorem moduleCatHasInjectiveResolutions (S : Scheme.{u}) :
    HasInjectiveResolutions
      (RingedSite.ModuleCat.{u + 1} (ringedSite S)) := sorry

/-- The degree-`i` higher direct image of a module sheaf along the small
étale-site morphism induced by a scheme morphism. -/
noncomputable def higherDirectImageModule {S T : Scheme.{u}} (f : T ⟶ S)
    (ℱ : RingedSite.ModuleCat.{u + 1} (ringedSite T)) (i : ℕ) :
    RingedSite.ModuleCat.{u + 1} (ringedSite S) :=
  @RingedSite.Hom.higherDirectImageModule
    (ringedSite T) (ringedSite S) (ringedHom f)
    inferInstance inferInstance (moduleCatHasInjectiveResolutions T) ℱ i

end AlgebraicGeometry.Scheme.Etale.Small
