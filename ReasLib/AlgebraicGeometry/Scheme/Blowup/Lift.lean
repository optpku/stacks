/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.BaseChange

/-!
# Lifts to admissible blowups

Morphisms landing in the distinguished open of an admissible blowup lift canonically to the
blowup. This file also constructs the induced lift to a fiber product and records its basic
properties.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/-- The canonical lift of a morphism landing in the open of an admissible blowup. -/
noncomputable def liftAdmissible
    {W X X' : Scheme.{u}} (U : X.Opens) (b : X' ⟶ X) (I : X.IdealSheafData)
    [hI : IsAdmissibleBlowupCenter U b I] (h : W ⟶ X)
    (hU : Set.range h.base ⊆ Set.range U.ι.base) : W ⟶ X' :=
  IsOpenImmersion.lift U.ι h hU ≫
    (@asIso _ _ _ _ (b ∣_ U)
      (Scheme.Hom.isIso_restrict_of_le b hI.disjoint_support.le_compl_left
        IsBlowup.isIso_restrict_compl_support)).inv ≫
      (b ⁻¹ᵁ U).ι

/-- The admissible lift composes with the blowup morphism to the original morphism. -/
@[reassoc]
theorem liftAdmissible_fac
    {W X X' : Scheme.{u}} (U : X.Opens) (b : X' ⟶ X) (I : X.IdealSheafData)
    [IsAdmissibleBlowupCenter U b I] (h : W ⟶ X)
    (hU : Set.range h.base ⊆ Set.range U.ι.base) :
    liftAdmissible U b I h hU ≫ b = h := sorry

/-- The admissible lift is independent of the chosen admissible-center presentation. -/
theorem liftAdmissible_independent
    {W X X' : Scheme.{u}} (U : X.Opens) (b : X' ⟶ X)
    (I J : X.IdealSheafData)
    [IsAdmissibleBlowupCenter U b I] [IsAdmissibleBlowupCenter U b J]
    (h : W ⟶ X) (hU : Set.range h.base ⊆ Set.range U.ι.base) :
    liftAdmissible U b I h hU = liftAdmissible U b J h hU := sorry

/-- The two legs defining the lifted morphism to the new pullback commute. -/
theorem liftAdmissiblePullback_condition
    {S X Y V X' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (q : V ⟶ pullback f g) (U : X.Opens) (b : X' ⟶ X)
    (I : X.IdealSheafData) [IsAdmissibleBlowupCenter U b I]
    (hU : Set.range (q ≫ pullback.fst f g).base ⊆ Set.range U.ι.base) :
    liftAdmissible U b I (q ≫ pullback.fst f g) hU ≫ (b ≫ f) =
      (q ≫ pullback.snd f g) ≫ g := sorry

/-- The morphism to `X' ×_S Y` induced by lifting the first projection of `q` across an
admissible blowup. -/
noncomputable def liftAdmissiblePullback
    {S X Y V X' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (q : V ⟶ pullback f g) (U : X.Opens) (b : X' ⟶ X)
    (I : X.IdealSheafData) [IsAdmissibleBlowupCenter U b I]
    (hU : Set.range (q ≫ pullback.fst f g).base ⊆ Set.range U.ι.base) :
    V ⟶ pullback (b ≫ f) g :=
  pullback.lift
    (liftAdmissible U b I (q ≫ pullback.fst f g) hU)
    (q ≫ pullback.snd f g)
    (liftAdmissiblePullback_condition f g q U b I hU)

/-- The first projection of the lifted pullback morphism is the admissible lift. -/
@[reassoc]
theorem liftAdmissiblePullback_fst
    {S X Y V X' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (q : V ⟶ pullback f g) (U : X.Opens) (b : X' ⟶ X)
    (I : X.IdealSheafData) [IsAdmissibleBlowupCenter U b I]
    (hU : Set.range (q ≫ pullback.fst f g).base ⊆ Set.range U.ι.base) :
    liftAdmissiblePullback f g q U b I hU ≫ pullback.fst (b ≫ f) g =
      liftAdmissible U b I (q ≫ pullback.fst f g) hU := sorry

/-- The second projection of the lifted pullback morphism agrees with that of `q`. -/
@[reassoc]
theorem liftAdmissiblePullback_snd
    {S X Y V X' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (q : V ⟶ pullback f g) (U : X.Opens) (b : X' ⟶ X)
    (I : X.IdealSheafData) [IsAdmissibleBlowupCenter U b I]
    (hU : Set.range (q ≫ pullback.fst f g).base ⊆ Set.range U.ι.base) :
    liftAdmissiblePullback f g q U b I hU ≫ pullback.snd (b ≫ f) g =
      q ≫ pullback.snd f g := sorry

/-- The lifted pullback morphism is independent of the admissible-center presentation. -/
theorem liftAdmissiblePullback_independent
    {S X Y V X' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (q : V ⟶ pullback f g) (U : X.Opens) (b : X' ⟶ X)
    (I J : X.IdealSheafData)
    [IsAdmissibleBlowupCenter U b I] [IsAdmissibleBlowupCenter U b J]
    (hU : Set.range (q ≫ pullback.fst f g).base ⊆ Set.range U.ι.base) :
    liftAdmissiblePullback f g q U b I hU =
      liftAdmissiblePullback f g q U b J hU := sorry

/-- Quasi-compactness is preserved by the canonical lift to the blown-up pullback. -/
instance instQuasiCompactLiftAdmissiblePullback
    {S X Y V X' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (q : V ⟶ pullback f g) [QuasiCompact q]
    (U : X.Opens) (b : X' ⟶ X) (I : X.IdealSheafData)
    [IsAdmissibleBlowupCenter U b I]
    (hU : Set.range (q ≫ pullback.fst f g).base ⊆ Set.range U.ι.base) :
    QuasiCompact (liftAdmissiblePullback f g q U b I hU) := sorry

end Scheme.Hom

end AlgebraicGeometry
