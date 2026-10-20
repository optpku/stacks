/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.PuncturedStalk
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over.StalkGluing.Neighborhood

/-!
# Morphism properties under punctured-local base change

This file records preservation and reflection of standard properties of finite-presentation
morphisms under the punctured-local base-change correspondence.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.puncturedLocalBaseChange

/-- Separatedness is preserved and reflected by the punctured-local base-change correspondence. -/
theorem isSeparated_iff
    (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
    (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
    (hUqc : QuasiCompact U.ι)
    (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
    (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
      ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
        Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ)
    (X : FinitePresentationIsoOverOpen U)
    (Y : FinitePresentationIsoOverOpen V)
    (e : (puncturedLocalBaseChange S s hs U hU hUqc V hV).obj X ≅ Y) :
    IsSeparated X.obj.hom ↔ IsSeparated Y.obj.hom := sorry

/-- Properness is preserved and reflected by the punctured-local base-change correspondence. -/
theorem isProper_iff
    (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
    (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
    (hUqc : QuasiCompact U.ι)
    (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
    (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
      ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
        Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ)
    (X : FinitePresentationIsoOverOpen U)
    (Y : FinitePresentationIsoOverOpen V)
    (e : (puncturedLocalBaseChange S s hs U hU hUqc V hV).obj X ≅ Y) :
    IsProper X.obj.hom ↔ IsProper Y.obj.hom := sorry

/-- Finiteness is preserved and reflected by the punctured-local base-change correspondence. -/
theorem isFinite_iff
    (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
    (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
    (hUqc : QuasiCompact U.ι)
    (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
    (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
      ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
        Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ)
    (X : FinitePresentationIsoOverOpen U)
    (Y : FinitePresentationIsoOverOpen V)
    (e : (puncturedLocalBaseChange S s hs U hU hUqc V hV).obj X ≅ Y) :
    IsFinite X.obj.hom ↔ IsFinite Y.obj.hom := sorry

/-- Étaleness is preserved and reflected by the punctured-local base-change correspondence. -/
theorem etale_iff
    (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
    (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
    (hUqc : QuasiCompact U.ι)
    (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
    (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
      ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
        Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ)
    (X : FinitePresentationIsoOverOpen U)
    (Y : FinitePresentationIsoOverOpen V)
    (e : (puncturedLocalBaseChange S s hs U hU hUqc V hV).obj X ≅ Y) :
    Etale X.obj.hom ↔ Etale Y.obj.hom := sorry

/-- Integrality is preserved and reflected by the punctured-local base-change correspondence. -/
theorem isIntegralHom_iff
    (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
    (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
    (hUqc : QuasiCompact U.ι)
    (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
    (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
      ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
        Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ)
    (X : FinitePresentationIsoOverOpen U)
    (Y : FinitePresentationIsoOverOpen V)
    (e : (puncturedLocalBaseChange S s hs U hU hUqc V hV).obj X ≅ Y) :
    IsIntegralHom X.obj.hom ↔ IsIntegralHom Y.obj.hom := sorry

end AlgebraicGeometry.puncturedLocalBaseChange
