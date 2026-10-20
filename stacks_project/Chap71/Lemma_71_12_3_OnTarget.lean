/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap71.Lemma_71_11_11_Triple
public import stacks_project.Chap71.Lemma_71_12_2_Map

/-!
# Relative projective-spectrum maps on the full source

This file transports a relative projective-spectrum map of algebraic spaces and
its twist comparisons from the natural open domain to the full source when that
domain is the identity open subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Sheaf.InternalModule
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProjMap

variable {S : Scheme.{u}}

/-- Restriction of modules along an identity morphism is the identity on underlying
sheaves. -/
def restrictFunctorId (Q : AlgebraicSpace S) :
    Modules.restrictFunctor (𝟙 Q) ≅ 𝟭 Q.Modules :=
  NatIso.ofComponents
    (fun M ↦
      { hom :=
          homOfUnderlying (structureSheaf Q)
            (InducedCategory.homMk
              { app := fun _ ↦ 𝟙 _
                naturality := fun _ _ _ ↦ sorry })
            sorry sorry
        inv :=
          homOfUnderlying (structureSheaf Q)
            (InducedCategory.homMk
              { app := fun _ ↦ 𝟙 _
                naturality := fun _ _ _ ↦ sorry })
            sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Pullbacks of module sheaves along equal morphisms of algebraic spaces are
isomorphic. -/
def pullbackCongr {Y Z : AlgebraicSpace S} {f g : Y ⟶ Z} (h : f = g) :
    Modules.pullback f ≅ Modules.pullback g :=
  eqToIso (congrArg Modules.pullback h)

/-- `pullbackCongr` is functoriality of module pullback on equal morphisms. -/
theorem pullbackCongr_eq {Y Z : AlgebraicSpace S} {f g : Y ⟶ Z} (h : f = g) :
    pullbackCongr h = eqToIso (congrArg Modules.pullback h) :=
  sorry

/-- Pullback of modules along an identity morphism is canonically the identity. -/
def pullbackId (Q : AlgebraicSpace S) :
    Modules.pullback (𝟙 Q) ≅ 𝟭 Q.Modules :=
  (Modules.restrictFunctorIsoPullback (𝟙 Q)).symm ≪≫ restrictFunctorId Q

/-- `pullbackId` is étale restriction along the identity, compared with module
pullback. -/
theorem pullbackId_eq (Q : AlgebraicSpace S) :
    pullbackId Q =
      (Modules.restrictFunctorIsoPullback (𝟙 Q)).symm ≪≫ restrictFunctorId Q :=
  sorry

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
    (pullbackCongr hι).hom.app (twistQ n) ≫
    (pullbackId Q).hom.app (twistQ n)

end AlgebraicGeometry.AlgebraicSpace.RelativeProjMap
