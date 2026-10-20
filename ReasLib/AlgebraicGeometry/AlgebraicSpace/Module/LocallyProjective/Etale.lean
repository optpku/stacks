/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.LocallyProjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.Basic

/-!
# Local projectivity on étale scheme charts

For a quasi-coherent module on an algebraic space, local projectivity on one surjective
étale scheme chart is equivalent to local projectivity on every étale scheme chart.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The restriction of a module along an étale scheme morphism is locally projective on
the underlying scheme. -/
def isLocallyProjectiveOn {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    {U : Over S} (f : ofOver U ⟶ X) [hf : Etale f] : Prop :=
  AlgebraicGeometry.Scheme.Modules.IsLocallyProjective
    ((restrictToScheme U).obj (restrict F f))

/-- There is a surjective étale scheme chart on which the restricted module is locally
projective. -/
def existsSurjectiveEtale {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) : Prop :=
  ∃ (U : Over S) (f : ofOver U ⟶ X) (hf : Etale f),
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f ∧
      isLocallyProjectiveOn F f (hf := hf)

/-- The restriction of a module to every étale scheme chart is locally projective on the
underlying scheme. -/
def forallEtale {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) : Prop :=
  ∀ (U : Over S) (f : ofOver U ⟶ X) [Etale f], isLocallyProjectiveOn F f

/-- For a quasi-coherent module, local projectivity on an étale scheme chart agrees with
local projectivity of its restriction as an algebraic-space module. -/
theorem isLocallyProjectiveOn_iff {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent] {U : Over S} (f : ofOver U ⟶ X) [hf : Etale f] :
    isLocallyProjectiveOn F f ↔ IsLocallyProjective (restrict F f) := by
  sorry

/-- A quasi-coherent module is locally projective on some surjective étale scheme chart
if and only if it is locally projective on every étale scheme chart. -/
theorem existsSurjectiveEtale_iff_forallEtale {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] : existsSurjectiveEtale F ↔ forallEtale F := by
  constructor
  · rintro ⟨U, f, hf, hsurj, hF⟩
    have h : IsLocallyProjective F :=
      (isLocallyProjective_iff_exists_surjective_etale F).mpr
        ⟨U, f, hf, hsurj, (isLocallyProjectiveOn_iff F f (hf := hf)).mp hF⟩
    intro V g hg
    exact (isLocallyProjectiveOn_iff F g).mpr
      ((isLocallyProjective_iff_forall_etale F).mp h V g)
  · intro hF
    have h : IsLocallyProjective F :=
      (isLocallyProjective_iff_forall_etale F).mpr (fun U f hf =>
        (isLocallyProjectiveOn_iff F f).mp (hF U f))
    obtain ⟨U, f, hf, hsurj, hU⟩ :=
      (isLocallyProjective_iff_exists_surjective_etale F).mp h
    exact ⟨U, f, hf, hsurj, (isLocallyProjectiveOn_iff F f (hf := hf)).mpr hU⟩

end AlgebraicGeometry.AlgebraicSpace.Modules
