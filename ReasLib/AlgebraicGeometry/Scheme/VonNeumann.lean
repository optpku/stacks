/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.SmallBoundClosed
public import Mathlib.SetTheory.ZFC.VonNeumann

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Cardinal AlgebraicGeometry
open scoped ZFSet

namespace AlgebraicGeometry.Scheme

universe u

/-- A scheme presented on actual sets: both its point type and each section-ring carrier
are the small types of elements of specified ZFC sets. The carrier equalities exclude
unrecorded type labels from the presentation's set code. -/
structure SetPresentation where
  /-- The scheme realized by the presentation. -/
  scheme : Scheme.{u}
  /-- The set of point labels. -/
  pointSet : ZFSet.{u}
  /-- The point carrier is the small type of elements of `pointSet`. -/
  pointCarrier : (scheme : Type u) = Shrink pointSet
  /-- The set of section labels over each open. -/
  sectionSet : scheme.Opens → ZFSet.{u}
  /-- Every section-ring carrier is the small type of elements of its label set. -/
  sectionCarrier (U : scheme.Opens) :
    (Γ(scheme, U) : Type u) = Shrink (sectionSet U)

namespace SetPresentation

/-- Realize a set presentation as a native scheme. -/
def toScheme (S : SetPresentation.{u}) : Scheme.{u} := S.scheme

/-- The set label of a point. -/
def pointVal (S : SetPresentation.{u}) (x : S.scheme) : ZFSet.{u} :=
  ((equivShrink S.pointSet).symm (cast S.pointCarrier x)).val

/-- Encode an open by its set of point labels. -/
def openCode (S : SetPresentation.{u}) (U : S.scheme.Opens) : ZFSet.{u} :=
  ZFSet.range (fun x : U ↦ S.pointVal x.val)

/-- The set label of a section. -/
def sectionVal (S : SetPresentation.{u}) (U : S.scheme.Opens)
    (s : Γ(S.scheme, U)) : ZFSet.{u} :=
  ((equivShrink (S.sectionSet U)).symm (cast (S.sectionCarrier U) s)).val

/-- Encode a section ring by its carrier, constants, and operation graphs. -/
def ringCode (S : SetPresentation.{u}) (U : S.scheme.Opens) : ZFSet.{u} :=
  ZFSet.pair (S.sectionSet U)
    (ZFSet.pair (S.sectionVal U 0)
      (ZFSet.pair (S.sectionVal U 1)
        (ZFSet.pair
          (ZFSet.range (fun s : Γ(S.scheme, U) ↦
            ZFSet.pair (S.sectionVal U s) (S.sectionVal U (-s))))
          (ZFSet.pair
            (ZFSet.range (fun st : Γ(S.scheme, U) × Γ(S.scheme, U) ↦
              ZFSet.pair (ZFSet.pair (S.sectionVal U st.1) (S.sectionVal U st.2))
                (S.sectionVal U (st.1 + st.2))))
            (ZFSet.range (fun st : Γ(S.scheme, U) × Γ(S.scheme, U) ↦
              ZFSet.pair (ZFSet.pair (S.sectionVal U st.1) (S.sectionVal U st.2))
                (S.sectionVal U (st.1 * st.2))))))))

/-- Encode all restriction maps, recording their source and target opens. -/
def restrictionCode (S : SetPresentation.{u}) : ZFSet.{u} :=
  ZFSet.range (fun UV : { UV : S.scheme.Opens × S.scheme.Opens // UV.1 ≤ UV.2 } ↦
    ZFSet.pair (S.openCode UV.val.1)
      (ZFSet.pair (S.openCode UV.val.2)
        (ZFSet.range (fun s : Γ(S.scheme, UV.val.2) ↦
          ZFSet.pair (S.sectionVal UV.val.2 s)
            (S.sectionVal UV.val.1
              ((S.scheme.presheaf).map (homOfLE UV.property).op s))))))

/-- The complete set code: points, open sets with their section rings, and restrictions.
The remaining scheme fields are proof laws and carry no further set data. -/
def code (S : SetPresentation.{u}) : ZFSet.{u} :=
  ZFSet.pair S.pointSet
    (ZFSet.pair
      (ZFSet.range (fun U : S.scheme.Opens ↦ ZFSet.pair (S.openCode U) (S.ringCode U)))
      S.restrictionCode)

/-- The complete set code determines the presentation, including its realized scheme. -/
theorem code_injective : Function.Injective (code : SetPresentation.{u} → ZFSet.{u}) := sorry

/-- Every native scheme admits an isomorphic presentation on actual sets. -/
theorem exists_iso (X : Scheme.{u}) :
    ∃ S : SetPresentation.{u}, Nonempty (X ≅ S.toScheme) := sorry

end SetPresentation

/-- The native full subcategory `Sch_α`: schemes realized by set presentations whose
complete codes belong to `V_α`. All set codes and the stage ordinal use the same universe. -/
def vonNeumannStage (α : Ordinal.{u}) : ObjectProperty Scheme.{u} :=
  fun X ↦ ∃ S : SetPresentation.{u}, S.toScheme = X ∧ S.code ∈ V_ α

/-- Membership in `Sch_α` is membership of a realizing presentation's complete code in `V_α`. -/
theorem mem_vonNeumannStage_iff (α : Ordinal.{u}) (X : Scheme.{u}) :
    vonNeumannStage α X ↔
      ∃ S : SetPresentation.{u}, S.toScheme = X ∧ S.code ∈ V_ α := Iff.rfl

/-- Every small family of set-presented schemes is contained in a limit level `V_α`.
The full subcategory `vonNeumannStage α` represents all schemes within the prescribed
size bound and detects countable limits and colimits, with the canonical ambient
comparison morphisms being isomorphisms. -/
theorem exists_isSmallBoundClosed {ι : Type u} (S0 : ι → SetPresentation.{u}) :
    ∃ α : Ordinal.{u}, Order.IsSuccLimit α ∧
      IsSmallBoundClosed (vonNeumannStage α) ∧
      (∀ i, (S0 i).code ∈ V_ α) ∧
      ObjectProperty.ofObj (fun i ↦ (S0 i).toScheme) ≤ vonNeumannStage α := sorry

end AlgebraicGeometry.Scheme
