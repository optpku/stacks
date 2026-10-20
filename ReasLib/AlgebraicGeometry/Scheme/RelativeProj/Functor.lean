/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Representability
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.Transition

/-!
# Relative projective-spectrum functors

This module packages a relative projective-spectrum functor together with its
representable positive-degree open charts, their canonical quadruple classifications,
and a covering map compatible with the specified degree transitions.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {S : Scheme.{u}}
variable (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf)

/-- A relative projective-spectrum functor together with its representable
positive-degree open charts and their joint Zariski cover. -/
class RelativeProjFunctor
    (S : Scheme.{u}) (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) where
  /-- The graded algebra is quasi-coherent in every degree. -/
  algebra_isQuasicoherent : ∀ n : ℤ, (𝒜 n).IsQuasicoherent
  /-- The ambient relative projective-spectrum functor as a Zariski sheaf on schemes. -/
  toSheaf : Sheaf Scheme.zariskiTopology (Type u)
  /-- The standard chart functor in each positive degree. -/
  degreeFunctor : ∀ d : { n : ℕ // 1 ≤ n }, Scheme.RelativeProjDegreeFunctor S 𝒜 d.1
  /-- The canonical degreewise identification with geometric quadruples. -/
  degreeAssociated : ∀ d : { n : ℕ // 1 ≤ n }, (degreeFunctor d).IsAssociatedToQuadruples
  /-- Every positive-degree chart functor is representable. -/
  degreeFunctor_isRepresentable :
    ∀ d : { n : ℕ // 1 ≤ n }, (degreeFunctor d).toFunctor.IsRepresentable
  /-- The canonical map from each positive-degree chart to the ambient functor. -/
  degreeToFunctor :
    ∀ d : { n : ℕ // 1 ≤ n }, (degreeFunctor d).toFunctor ⟶ toSheaf.1
  /-- The ambient chart maps respect the actual tensor-power/Veronese transitions.
  This is part of the relative-Proj presentation, not a theorem about arbitrary
  independently glued copies of the degree charts. -/
  degreeToFunctor_transition :
    ∀ (d e : { n : ℕ // 1 ≤ n }) (h : d.1 ∣ e.1),
      (degreeAssociated d).transition (degreeAssociated e) h ≫ degreeToFunctor e =
        degreeToFunctor d
  /-- Each canonical chart map is a relatively representable open immersion of presheaves. -/
  degreeToFunctor_isOpenImmersion :
    ∀ d : { n : ℕ // 1 ≤ n }, IsOpenImmersion.presheaf (degreeToFunctor d)
  /-- The positive-degree chart maps jointly cover the ambient functor in the big Zariski
  topology. -/
  coveredByDegree :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc degreeToFunctor)

namespace RelativeProjFunctor

/-- The contravariant set-valued functor carried by a relative projective-spectrum functor. -/
abbrev toFunctor
    (F : RelativeProjFunctor S 𝒜) : Schemeᵒᵖ ⥤ Type u :=
  F.toSheaf.1

/-- A relative projective-spectrum functor covered by representable open charts is
representable. -/
instance instIsRepresentable
    [F : RelativeProjFunctor S 𝒜] :
    F.toFunctor.IsRepresentable := by
  letI (d : {n : ℕ // 1 ≤ n}) : (F.degreeFunctor d).toFunctor.IsRepresentable :=
    F.degreeFunctor_isRepresentable d
  let charts (d : ULift.{u} {n : ℕ // 1 ≤ n}) := (F.degreeFunctor d.down).toFunctor.reprX
  let maps (d : ULift.{u} {n : ℕ // 1 ≤ n}) : yoneda.obj (charts d) ⟶ F.toSheaf.obj :=
    (F.degreeFunctor d.down).toFunctor.reprW.hom ≫ F.degreeToFunctor d.down
  have maps_open (d : ULift.{u} {n : ℕ // 1 ≤ n}) : IsOpenImmersion.presheaf (maps d) :=
    MorphismProperty.comp_mem IsOpenImmersion.presheaf _ _
      (MorphismProperty.of_isIso IsOpenImmersion.presheaf _)
      (F.degreeToFunctor_isOpenImmersion d.down)
  let reindex :
      (∐ fun d : ULift.{u} {n : ℕ // 1 ≤ n} ↦ (F.degreeFunctor d.down).toFunctor) ≅
        ∐ fun d ↦ (F.degreeFunctor d).toFunctor :=
    { hom := Limits.Sigma.map' ULift.down (fun _ ↦ 𝟙 _)
      inv := Limits.Sigma.map' ULift.up (fun _ ↦ 𝟙 _)
      hom_inv_id := by
        apply Limits.Sigma.hom_ext
        intro d
        simp only [Limits.Sigma.ι_comp_map'_assoc,
          Limits.Sigma.ι_comp_map', Category.id_comp, Category.comp_id, ULift.up_down]
      inv_hom_id := by
        apply Limits.Sigma.hom_ext
        intro d
        simp only [Limits.Sigma.ι_comp_map'_assoc,
          Limits.Sigma.ι_comp_map', Category.id_comp, Category.comp_id] }
  let e := Limits.Sigma.mapIso (fun d : ULift.{u} {n : ℕ // 1 ≤ n} ↦
    (F.degreeFunctor d.down).toFunctor.reprW) ≪≫ reindex
  have fac : e.hom ≫ Limits.Sigma.desc F.degreeToFunctor = Limits.Sigma.desc maps := by
    apply Limits.Sigma.hom_ext
    intro d
    simp only [e, Iso.trans_hom, Category.assoc, Limits.Sigma.ι_mapIso_hom_assoc]
    simp only [reindex, Limits.Sigma.ι_comp_map'_assoc, Category.id_comp,
      Limits.Sigma.ι_desc]
    rfl
  letI := F.coveredByDegree
  letI : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc maps) := by
    rw [← fac]
    infer_instance
  exact Scheme.LocalRepresentability.isRepresentable
    (F := F.toSheaf) (X := charts) (f := maps) maps_open

end RelativeProjFunctor

end

end AlgebraicGeometry
