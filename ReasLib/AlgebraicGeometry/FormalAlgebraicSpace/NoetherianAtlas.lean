/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Types

/-!
# Noetherian atlases and adic affine presentations

A locally Noetherian formal algebraic space admits an étale atlas by Noetherian
affine formal spaces. Their adic presentations determine complete chart rings,
ideals of definition, quotient-power diagrams, and comparison cocones.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace
open IsLocalRing Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The chosen index type of a locally Noetherian étale atlas. -/
def atlasIndex {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] : Type u :=
  Classical.choose ‹IsLocallyNoetherian X›.exists_noetherian_atlas

/-- The chosen Noetherian affine charts of a locally Noetherian étale atlas. -/
def atlasCover {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] :
    atlasIndex X → ((Over S)ᵒᵖ ⥤ Type u) :=
  Classical.choose (Classical.choose_spec ‹IsLocallyNoetherian X›.exists_noetherian_atlas)

/-- The chosen morphisms from the Noetherian affine charts into `X`. -/
def atlasπ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] :
    (i : atlasIndex X) → atlasCover X i ⟶ X :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec ‹IsLocallyNoetherian X›.exists_noetherian_atlas))

/-- Each chosen atlas chart is a Noetherian affine formal algebraic space. -/
instance instIsNoetherianAffine_atlasCover {S : Scheme.{u}}
    (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (i : atlasIndex X) : IsNoetherianAffine (atlasCover X i) :=
  (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec ‹IsLocallyNoetherian X›.exists_noetherian_atlas))).1 i

/-- The adic Noetherian ring presenting a Noetherian affine formal algebraic
space. -/
def chartRing {S : Scheme.{u}} (U : (Over S)ᵒᵖ ⥤ Type u)
    [IsNoetherianAffine U] : Type u :=
  Classical.choose ‹IsNoetherianAffine U›.exists_adicNoetherian

/-- The ring structure of `chartRing U`. -/
instance instCommRing_chartRing {S : Scheme.{u}} (U : (Over S)ᵒᵖ ⥤ Type u)
    [IsNoetherianAffine U] : CommRing (chartRing U) :=
  Classical.choose (Classical.choose_spec ‹IsNoetherianAffine U›.exists_adicNoetherian)

/-- The topology of `chartRing U`. -/
instance instTopologicalSpace_chartRing {S : Scheme.{u}}
    (U : (Over S)ᵒᵖ ⥤ Type u) [IsNoetherianAffine U] :
    TopologicalSpace (chartRing U) :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec ‹IsNoetherianAffine U›.exists_adicNoetherian))

/-- `chartRing U` is an adic topological ring. -/
instance instIsAdicRing_chartRing {S : Scheme.{u}} (U : (Over S)ᵒᵖ ⥤ Type u)
    [IsNoetherianAffine U] : TopologicalRing.IsAdicRing (chartRing U) :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec ‹IsNoetherianAffine U›.exists_adicNoetherian)))

/-- `chartRing U` is Noetherian. -/
instance instIsNoetherianRing_chartRing {S : Scheme.{u}}
    (U : (Over S)ᵒᵖ ⥤ Type u) [IsNoetherianAffine U] :
    IsNoetherianRing (chartRing U) :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec ‹IsNoetherianAffine U›.exists_adicNoetherian))))

/-- The chosen ideal of definition of `chartRing U`. -/
def chartIdeal {S : Scheme.{u}} (U : (Over S)ᵒᵖ ⥤ Type u)
    [IsNoetherianAffine U] : Ideal (chartRing U) :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec
            (Classical.choose_spec ‹IsNoetherianAffine U›.exists_adicNoetherian)))))

/-- The selected ideal of the canonical affine presentation is an ideal of definition. -/
theorem chartIdeal_isIdealOfDefinition {S : Scheme.{u}}
    (U : (Over S)ᵒᵖ ⥤ Type u) [IsNoetherianAffine U] :
    TopologicalRing.Ideal.IsIdealOfDefinition (chartIdeal U) :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec
            (Classical.choose_spec
              (Classical.choose_spec ‹IsNoetherianAffine U›.exists_adicNoetherian))))))

/-- The selected ideal induces the actual topology and is complete. -/
theorem chartIdeal_properties {S : Scheme.{u}}
    (U : (Over S)ᵒᵖ ⥤ Type u) [IsNoetherianAffine U] :
    IsAdic (chartIdeal U) ∧ IsAdicComplete (chartIdeal U) (chartRing U) :=
  ⟨(chartIdeal_isIdealOfDefinition U).isAdic,
    (chartIdeal_isIdealOfDefinition U).isAdicComplete⟩

/-- The presenting ring is complete for its selected ideal of definition. -/
instance instIsAdicComplete_chartIdeal {S : Scheme.{u}}
    (U : (Over S)ᵒᵖ ⥤ Type u) [IsNoetherianAffine U] :
    IsAdicComplete (chartIdeal U) (chartRing U) :=
  (chartIdeal_properties U).2

/-- The structure morphism `Spec(chartRing U) ⟶ S`. -/
def chartStructureHom {S : Scheme.{u}} (U : (Over S)ᵒᵖ ⥤ Type u)
    [IsNoetherianAffine U] : Spec (.of (chartRing U)) ⟶ S :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec
            (Classical.choose_spec
              (Classical.choose_spec
                (Classical.choose_spec ‹IsNoetherianAffine U›.exists_adicNoetherian)))))))

/-- The `ℕ`-indexed thickening diagram of an adic Noetherian presentation. -/
def presentationDiagram {S : Scheme.{u}} (U : (Over S)ᵒᵖ ⥤ Type u)
    [IsNoetherianAffine U] : ℕ ⥤ Over S :=
  AffineFormalAlgebraicSpace.powerThickenings (chartStructureHom U) (chartIdeal U)

/-- The chosen canonical quotient-power diagram presents `U`. -/
instance instIsDirectedAffineThickeningColimit_presentationDiagram {S : Scheme.{u}}
    (U : (Over S)ᵒᵖ ⥤ Type u) [IsNoetherianAffine U] :
    IsDirectedAffineThickeningColimit (presentationDiagram U) U :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec
        (‹IsNoetherianAffine U›.exists_adicNoetherian))))))))

/-- Each presentation stage is an affine scheme. -/
instance instIsAffine_presentationDiagram_obj {S : Scheme.{u}}
    (U : (Over S)ᵒᵖ ⥤ Type u) [IsNoetherianAffine U] (n : ℕ) :
    AlgebraicGeometry.IsAffine ((presentationDiagram U).obj n).left :=
  (instIsDirectedAffineThickeningColimit_presentationDiagram U).isAffine_obj n

/-- Each presentation stage is the spectrum of the corresponding adic quotient. -/
def presentationStageIso {S : Scheme.{u}} (U : (Over S)ᵒᵖ ⥤ Type u)
    [IsNoetherianAffine U] (n : ℕ) :
    ((presentationDiagram U).obj n).left ≅
      Spec (.of (chartRing U ⧸ chartIdeal U ^ (n + 1))) :=
  Iso.refl _

/-- The chosen Yoneda cocone of the presentation diagram. -/
def presentationCocone {S : Scheme.{u}} (U : (Over S)ᵒᵖ ⥤ Type u)
    [IsNoetherianAffine U] : Cocone (presentationDiagram U ⋙ yoneda) :=
  Classical.choose
    (instIsDirectedAffineThickeningColimit_presentationDiagram U).exists_colimit

/-- The comparison from the presentation cocone point into `U`. -/
def presentationCoconeι {S : Scheme.{u}} (U : (Over S)ᵒᵖ ⥤ Type u)
    [IsNoetherianAffine U] : (presentationCocone U).pt ⟶ U :=
  Classical.choose
    (Classical.choose_spec
      (instIsDirectedAffineThickeningColimit_presentationDiagram U).exists_colimit)

/-- A Noetherian affine formal algebraic space is a formal algebraic space. -/
instance instIsFormalAlgebraicSpace_isNoetherianAffine {S : Scheme.{u}}
    (U : (Over S)ᵒᵖ ⥤ Type u) [IsNoetherianAffine U] :
    IsFormalAlgebraicSpace U :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
