/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Map.Partial

/-!
# Relative projective-spectrum maps on the full source

This file transports a relative projective-spectrum map of algebraic spaces and
its twist comparisons from the natural open domain to the full source when the
domain is the identity open subspace or its inclusion is invertible.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Sheaf.InternalModule
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProjMap

variable {S : Scheme.{u}}

variable {X P Q : AlgebraicSpace S}
variable {πP : P ⟶ X} {πQ : Q ⟶ X}
variable {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
variable {twistP : ℤ → P.Modules} {twistQ : ℤ → Q.Modules}
variable {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}

/-- The canonical morphism from the full source algebraic space to the natural
domain of a relative projective-spectrum map when that domain is the identity
open subspace. -/
abbrev domainTopInclusion
    (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (hTop : r.domain = OpenSubspace.id Q) :
    Q ⟶ r.domain.X :=
  eqToHom (congrArg OpenSubspace.X hTop.symm)

/-- The canonical morphism from the full source to an identity-open natural domain
is inverse to the domain inclusion. -/
theorem domainTopInclusion_comp_ι
    (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (hTop : r.domain = OpenSubspace.id Q) :
    domainTopInclusion r hTop ≫ r.domain.ι = 𝟙 Q :=
  sorry

/-- A relative projective-spectrum map extends from its natural domain to the full
source algebraic space when that domain is the identity open subspace. -/
abbrev mapOnTarget
    (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (hTop : r.domain = OpenSubspace.id Q) :
    Q ⟶ P :=
  domainTopInclusion r hTop ≫ r.map

/-- A twist comparison for a relative projective-spectrum map extends from its
natural domain to the full source algebraic space when the domain inclusion has an
explicit inverse law. -/
abbrev thetaOnTarget
    (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (hTop : r.domain = OpenSubspace.id Q)
    (hι : domainTopInclusion r hTop ≫ r.domain.ι = 𝟙 Q)
    (n : ℤ) :
    (Modules.pullback (mapOnTarget r hTop)).obj (twistP n) ⟶ twistQ n :=
  let i : Q ⟶ r.domain.X := domainTopInclusion r hTop
  (Modules.pullbackCompIso i r.map).inv.app (twistP n) ≫
    (Modules.pullback i).map (r.theta n) ≫
    (Modules.pullbackCompIso i r.domain.ι).hom.app (twistQ n) ≫
    (Modules.pullbackCongr hι).hom.app (twistQ n) ≫
    (Modules.pullbackIdIso Q).hom.app (twistQ n)

/-- A relative projective-spectrum map extends to the full source by composing
with the canonical inverse of its invertible domain inclusion. -/
abbrev mapOfFullDomain
    (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (hFull : IsIso r.domain.ι) :
    Q ⟶ P :=
  CategoryTheory.inv r.domain.ι (I := hFull) ≫ r.map

/-- The twist comparison of a relative projective-spectrum map transports to the
full source along the canonical inverse of its invertible domain inclusion. -/
abbrev thetaOfFullDomain
    (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (hFull : IsIso r.domain.ι)
    (n : ℤ) :
    (Modules.pullback (mapOfFullDomain r hFull)).obj (twistP n) ⟶ twistQ n :=
  let i : Q ⟶ r.domain.X := CategoryTheory.inv r.domain.ι (I := hFull)
  let hι : i ≫ r.domain.ι = 𝟙 Q := IsIso.inv_hom_id r.domain.ι (I := hFull)
  (Modules.pullbackCompIso i r.map).inv.app (twistP n) ≫
    (Modules.pullback i).map (r.theta n) ≫
    (Modules.pullbackCompIso i r.domain.ι).hom.app (twistQ n) ≫
    (Modules.pullbackCongr hι).hom.app (twistQ n) ≫
    (Modules.pullbackIdIso Q).hom.app (twistQ n)

end AlgebraicGeometry.AlgebraicSpace.RelativeProjMap
