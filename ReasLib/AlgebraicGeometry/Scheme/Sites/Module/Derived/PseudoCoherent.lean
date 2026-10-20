module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Derived.EtaleRestriction

/-!
# Pseudo-coherence under small étale inverse image

An object of `D(𝒪_X)` is `m`-pseudo-coherent if and only if its exact derived
inverse image from the small Zariski site to the small étale site is
`m`-pseudo-coherent.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule
open AlgebraicGeometry.Scheme.SiteRestriction
open CategoryTheory
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SiteRestriction

/-- Exact derived inverse image along `commSmallEtaleToZariski` preserves
`m`-pseudo-coherence. -/
theorem commSmallEtaleToZariski_isMPseudoCoherent
    {X : Scheme.{u}} {E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)}
    {m : ℤ} (hE : E.IsMPseudoCoherent m) :
    ((commSmallEtaleToZariskiDerived X).obj E).IsMPseudoCoherent m :=
  sorry

/-- `m`-pseudo-coherence of the exact derived inverse image along
`commSmallEtaleToZariski` implies `m`-pseudo-coherence of the original object of
`D(𝒪_X)`. -/
theorem commSmallEtaleToZariski_isMPseudoCoherent_of_pullback
    {X : Scheme.{u}} (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X))
    {m : ℤ} :
    ((commSmallEtaleToZariskiDerived X).obj E).IsMPseudoCoherent m →
      E.IsMPseudoCoherent m :=
  sorry

/-- An object of `D(𝒪_X)` is `m`-pseudo-coherent if and only if its exact derived
inverse image along `commSmallEtaleToZariski` is `m`-pseudo-coherent on the small
étale site. -/
theorem commSmallEtaleToZariski_isMPseudoCoherent_iff
    {X : Scheme.{u}} (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X))
    (m : ℤ) :
    E.IsMPseudoCoherent m ↔
      ((commSmallEtaleToZariskiDerived X).obj E).IsMPseudoCoherent m :=
  ⟨commSmallEtaleToZariski_isMPseudoCoherent,
    commSmallEtaleToZariski_isMPseudoCoherent_of_pullback E⟩

/-- An object of `D(𝒪_X)` is pseudo-coherent if and only if its exact derived
inverse image along `commSmallEtaleToZariski` is pseudo-coherent on the small
étale site. -/
theorem commSmallEtaleToZariski_isPseudoCoherent_iff
    {X : Scheme.{u}} (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)) :
    E.IsPseudoCoherent ↔
      ((commSmallEtaleToZariskiDerived X).obj E).IsPseudoCoherent := by
  rw [RingedSite.DerivedCategory.isPseudoCoherent_iff E,
    RingedSite.DerivedCategory.isPseudoCoherent_iff
      ((commSmallEtaleToZariskiDerived X).obj E)]
  exact forall_congr' (fun m => commSmallEtaleToZariski_isMPseudoCoherent_iff E m)

end AlgebraicGeometry.Scheme.SiteRestriction
