/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Map.Basic

/-!
# Relative projective-spectrum maps on the full target

This file transports a relative projective-spectrum map and its twist comparisons from its
natural open domain to the full source scheme when that domain is top.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {S X Y : Scheme.{u}}
variable {pX : X ⟶ S} {pY : Y ⟶ S}
variable (P𝒜 : RelativeProjPresentation pX)
variable (Pℬ : RelativeProjPresentation pY)
variable (φ : P𝒜.algebra ⟶ Pℬ.algebra)

namespace RelativeProjMap

/-- The canonical morphism from the full source scheme to the natural domain of a relative
projective-spectrum map when that domain is top. -/
abbrev domainTopInclusion
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (hTop : rφ.domain = ⊤) :
    Y ⟶ rφ.domain.toScheme :=
  (Scheme.topIso Y).inv ≫ (Y.isoOfEq hTop.symm).hom

/-- The canonical morphism from the full source scheme to a top natural domain is inverse to
the domain inclusion. -/
theorem domainTopInclusion_comp_ι
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (hTop : rφ.domain = ⊤) :
    domainTopInclusion P𝒜 Pℬ φ rφ hTop ≫ rφ.domain.ι = 𝟙 Y := sorry

/-- A relative projective-spectrum map extends from its natural domain to the full source scheme
when that domain is top. -/
abbrev mapOnTarget
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (hTop : rφ.domain = ⊤) :
    Y ⟶ X :=
  domainTopInclusion P𝒜 Pℬ φ rφ hTop ≫ rφ.map

/-- A twist comparison for a relative projective-spectrum map extends from its natural domain
to the full source scheme when the domain inclusion has an explicit inverse law. -/
abbrev thetaOnTarget
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (hTop : rφ.domain = ⊤)
    (hι : domainTopInclusion P𝒜 Pℬ φ rφ hTop ≫ rφ.domain.ι = 𝟙 Y)
    (n : ℤ) :
    (Scheme.Modules.pullback (mapOnTarget P𝒜 Pℬ φ rφ hTop)).obj (P𝒜.twist n) ⟶
      Pℬ.twist n :=
  let i : Y ⟶ rφ.domain.toScheme := domainTopInclusion P𝒜 Pℬ φ rφ hTop
  ((Scheme.Modules.pullbackComp i rφ.map).inv.app (P𝒜.twist n)) ≫
    (Scheme.Modules.pullback i).map (rφ.theta n) ≫
    (Scheme.Modules.pullback i).map
      ((Scheme.Modules.restrictFunctorIsoPullback rφ.domain.ι).hom.app (Pℬ.twist n)) ≫
    ((Scheme.Modules.pullbackComp i rφ.domain.ι).hom.app (Pℬ.twist n)) ≫
    ((Scheme.Modules.pullbackCongr hι).hom.app (Pℬ.twist n)) ≫
    ((Scheme.Modules.pullbackId Y).hom.app (Pℬ.twist n))

end RelativeProjMap

end

end AlgebraicGeometry
