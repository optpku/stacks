/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.InjectiveResolution
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Pullback

/-!
# Standard big-site derived-image data

This compatibility module records the canonical site-morphism and
injective-resolution facts and the resulting explicit derived-image data for
standard big sites of schemes.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.StandardTopology.Big

/- Pullback along a scheme morphism is a morphism between the corresponding
standard big sites. -/
#check (pullback_isMorphismOfSites :
  ∀ (τ : StandardTopology) {S T : Scheme.{u}} (f : T ⟶ S),
    IsMorphismOfSites (τ.overTopology S) (τ.overTopology T)
      (Over.pullback f))

/- A scheme morphism induces an explicit morphism between the corresponding
standard big ringed sites. -/
#check (pullbackRingedHom :
  ∀ (τ : StandardTopology) {S T : Scheme.{u}},
    (T ⟶ S) → RingedSite.Hom (ringedSite τ T) (ringedSite τ S))

/- Module sheaves on a standard big site have injective resolutions at the
site's carrier universe. -/
#check (moduleCatHasInjectiveResolutions :
  ∀ (τ : StandardTopology) (S : Scheme.{u}),
    HasInjectiveResolutions
      (RingedSite.ModuleCat.{u + 1} (ringedSite τ S)))

/- Higher direct images on standard big sites use the canonical explicit
ringed-site morphism and injective-resolution fact. -/
#check (higherDirectImageModule :
  ∀ (τ : StandardTopology) {S T : Scheme.{u}},
    (T ⟶ S) → RingedSite.ModuleCat.{u + 1} (ringedSite τ T) → ℕ →
      RingedSite.ModuleCat.{u + 1} (ringedSite τ S))

end AlgebraicGeometry.StandardTopology.Big
