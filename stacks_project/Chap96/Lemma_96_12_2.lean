/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap96.«96_9_4_1_Comparison»
public import stacks_project.Chap96.Lemma_96_11_4_Comparison
public import stacks_project.Chap96.Lemma_96_12_4_LQCoh

/-!
# Lemma 96.12.2

A sheaf of `𝒪_X`-modules on a category fibred in groupoids is quasi-coherent
if and only if it is locally quasi-coherent and the comparison maps `c_φ` of
96.9.4.1 are isomorphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- Ring-to-abelian-group sheaf composition exists on every slice of the étale
ringed site of a category fibred in groupoids. -/
instance hasSheafCompose_etaleRingedSite_over :
    ∀ x, ((etaleRingedSite X).siteTopology.over x).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  associatedTopology_over_hasSheafCompose X .etale

/-- Weak sheafification of abelian groups exists on every slice of the étale
ringed site of a category fibred in groupoids. -/
instance hasWeakSheafify_etaleRingedSite_over :
    ∀ x, HasWeakSheafify ((etaleRingedSite X).siteTopology.over x)
      AddCommGrpCat.{u} :=
  associatedTopology_over_hasWeakSheafify X .etale

/-- Sheafification equivalences on slices of the étale ringed site of a category
fibred in groupoids are exactly the locally bijective morphisms. -/
instance wEqualsLocallyBijective_etaleRingedSite_over :
    ∀ x, ((etaleRingedSite X).siteTopology.over x).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  associatedTopology_over_wEqualsLocallyBijective X .etale

/-- Lemma 96.12.2: let `p : 𝒳 ⟶ (Sch/S)_fppf` be a category fibred in groupoids.
Let `F` be a presheaf of `𝒪_𝒳`-modules. Then `F` is quasi-coherent if and only
if `F` is locally quasi-coherent and, for any morphism `φ : x ⟶ y` of `𝒳`
lying over `f : U ⟶ V`, the comparison
`c_φ : f_small^*(F|_{V_étale}) ⟶ F|_{U_étale}` of 96.9.4.1 is an isomorphism.

On étale modules this is `F.IsQuasicoherent` if and only if
`IsLocallyQuasiCoherent F` and every `moduleComparison φ F` is an isomorphism.
The fppf presheaf packaging of Definition 96.11.1 is recovered by
`isQuasicoherentOn (etaleModulePresheaf F) .fppf`. -/
@[stacks 06WK]
theorem isQuasicoherent_iff_isLocallyQuasiCoherent (F : etaleModules X) :
    F.IsQuasicoherent ↔
      IsLocallyQuasiCoherent F ∧
        ∀ {x y : X.total} (φ : x ⟶ y), IsIso (moduleComparison φ F) :=
  sorry

/-- Quasi-coherence of the underlying fppf module presheaf, in the sense of
Definition 96.11.1, is equivalent to local quasi-coherence together with the
comparisons `moduleComparison φ F` of 96.9.4.1 being isomorphisms. -/
theorem isQuasicoherentOn_fppf_iff_isLocallyQuasiCoherent (F : etaleModules X) :
    isQuasicoherentOn (etaleModulePresheaf F) .fppf ↔
      IsLocallyQuasiCoherent F ∧
        ∀ {x y : X.total} (φ : x ⟶ y), IsIso (moduleComparison φ F) :=
  sorry

/-- Étale-site quasi-coherence of `F` is equivalent to fppf quasi-coherence of
the underlying module presheaf `etaleModulePresheaf F`. -/
theorem isQuasicoherent_iff_isQuasicoherentOn_fppf (F : etaleModules X) :
    F.IsQuasicoherent ↔ isQuasicoherentOn (etaleModulePresheaf F) .fppf :=
  sorry

/-- If `F` is locally quasi-coherent and every comparison `moduleComparison φ F`
is an isomorphism, then `F` is quasi-coherent. -/
theorem isQuasicoherent_of_isLocallyQuasiCoherent (F : etaleModules X)
    [IsLocallyQuasiCoherent F]
    (h : ∀ {x y : X.total} (φ : x ⟶ y), IsIso (moduleComparison φ F)) :
    F.IsQuasicoherent :=
  sorry

/-- A quasi-coherent étale `𝒪_X`-module is locally quasi-coherent. -/
instance instIsLocallyQuasiCoherent_of_isQuasicoherent (F : etaleModules X)
    [F.IsQuasicoherent] : IsLocallyQuasiCoherent F :=
  sorry

/-- If `F` is quasi-coherent, then the comparison `moduleComparison φ F` of
96.9.4.1 is an isomorphism. -/
instance instModuleComparison_isIso_of_isQuasicoherent (F : etaleModules X)
    [F.IsQuasicoherent] {x y : X.total} (φ : x ⟶ y) :
    IsIso (moduleComparison φ F) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
