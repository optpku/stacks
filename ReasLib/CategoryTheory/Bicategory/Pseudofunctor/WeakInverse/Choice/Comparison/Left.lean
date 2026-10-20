module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.WeakInverse.Choice.Construction
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Equivalence

/-!
# Source-side comparison for a chosen pseudoinverse

Local full faithfulness lifts the chosen object equivalences and their
naturality data to an equivalence from the source-side composite to the
identity.
-/

@[expose] public section

universe wB vB uB wC vC uC

namespace CategoryTheory.Pseudofunctor

open Bicategory
open scoped Bicategory Pseudofunctor.StrongTrans

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

namespace ChosenInverse

/-- The forward component at `X` of the source-side comparison. It is the
chosen local preimage of the forward object-equivalence morphism over
`F.obj X`. -/
noncomputable def leftApp (F : B ⥤ᵖ C) [F.IsBiequivalence] (X : B) :
    F.objPreimage (F.obj X) ⟶ X :=
  ((F.mapFunctor (F.objPreimage (F.obj X)) X).asEquivalence.inverse).obj
    (objPreimage.equivalence F (F.obj X)).hom

/-- The inverse component paired with `leftApp`. -/
noncomputable def leftInvApp (F : B ⥤ᵖ C) [F.IsBiequivalence] (X : B) :
    X ⟶ F.objPreimage (F.obj X) :=
  ((F.mapFunctor X (F.objPreimage (F.obj X))).asEquivalence.inverse).obj
    (objPreimage.equivalence F (F.obj X)).inv

/-- Mapping `leftApp` through `F` recovers the forward morphism of the chosen
object equivalence. -/
noncomputable def leftApp.mapIso (F : B ⥤ᵖ C) [F.IsBiequivalence] (X : B) :
    F.map (leftApp F X) ≅ (objPreimage.equivalence F (F.obj X)).hom :=
  let E := (F.mapFunctor (F.objPreimage (F.obj X)) X).asEquivalence
  E.counitIso.app (objPreimage.equivalence F (F.obj X)).hom

/-- Mapping `leftInvApp` through `F` recovers the inverse morphism of the
chosen object equivalence. -/
noncomputable def leftInvApp.mapIso (F : B ⥤ᵖ C) [F.IsBiequivalence] (X : B) :
    F.map (leftInvApp F X) ≅ (objPreimage.equivalence F (F.obj X)).inv :=
  let E := (F.mapFunctor X (F.objPreimage (F.obj X))).asEquivalence
  E.counitIso.app (objPreimage.equivalence F (F.obj X)).inv

/-- The image under `F` of the candidate unit for the source-side component
equivalence. -/
noncomputable def leftUnitImageIso (F : B ⥤ᵖ C) [F.IsBiequivalence] (X : B) :
    F.map (𝟙 (F.objPreimage (F.obj X))) ≅
      F.map (leftApp F X ≫ leftInvApp F X) :=
  F.mapId (F.objPreimage (F.obj X)) ≪≫
    (objPreimage.equivalence F (F.obj X)).unit ≪≫
    Bicategory.whiskerRightIso (leftApp.mapIso F X).symm
      (objPreimage.equivalence F (F.obj X)).inv ≪≫
    Bicategory.whiskerLeftIso (F.map (leftApp F X))
      (leftInvApp.mapIso F X).symm ≪≫
    (F.mapComp (leftApp F X) (leftInvApp F X)).symm

/-- The candidate unit for the source-side component equivalence, lifted
through local full faithfulness. -/
noncomputable def leftUnitIso (F : B ⥤ᵖ C) [F.IsBiequivalence] (X : B) :
    𝟙 (F.objPreimage (F.obj X)) ≅ leftApp F X ≫ leftInvApp F X :=
  (F.mapFunctor (F.objPreimage (F.obj X))
    (F.objPreimage (F.obj X))).preimageIso (leftUnitImageIso F X)

/-- The image under `F` of the counit for the source-side component
equivalence. -/
noncomputable def leftCounitImageIso (F : B ⥤ᵖ C) [F.IsBiequivalence] (X : B) :
    F.map (leftInvApp F X ≫ leftApp F X) ≅ F.map (𝟙 X) :=
  F.mapComp (leftInvApp F X) (leftApp F X) ≪≫
    Bicategory.whiskerRightIso (leftInvApp.mapIso F X)
      (F.map (leftApp F X)) ≪≫
    Bicategory.whiskerLeftIso
      (objPreimage.equivalence F (F.obj X)).inv
      (leftApp.mapIso F X) ≪≫
    (objPreimage.equivalence F (F.obj X)).counit ≪≫
    (F.mapId X).symm

/-- The counit for the source-side component equivalence, lifted through
local full faithfulness. -/
noncomputable def leftCounitIso (F : B ⥤ᵖ C) [F.IsBiequivalence] (X : B) :
    leftInvApp F X ≫ leftApp F X ≅ 𝟙 X :=
  (F.mapFunctor X X).preimageIso (leftCounitImageIso F X)

/-- The source-side component equivalence above `X`. -/
noncomputable def leftAppEquivalence (F : B ⥤ᵖ C) [F.IsBiequivalence] (X : B) :
    F.objPreimage (F.obj X) ≌ X :=
  Bicategory.Equivalence.mkOfAdjointifyUnit
    (leftUnitIso F X) (leftCounitIso F X)

/-- The image under `F` of the source-side naturality isomorphism. -/
noncomputable def leftNaturalityImageIso (F : B ⥤ᵖ C) [F.IsBiequivalence]
    {X Y : B} (f : X ⟶ Y) :
    F.map ((F.comp F.chosenInverse).map f ≫ leftApp F Y) ≅
      F.map (leftApp F X ≫ f) :=
  let eX := objPreimage.equivalence F (F.obj X)
  let eY := objPreimage.equivalence F (F.obj Y)
  let q := (eX.hom ≫ F.map f) ≫ eY.inv
  let E := (F.mapFunctor (F.objPreimage (F.obj X))
    (F.objPreimage (F.obj Y))).asEquivalence
  (F.mapComp ((F.comp F.chosenInverse).map f) (leftApp F Y) ≪≫
      Bicategory.whiskerRightIso (E.counitIso.app q)
        (F.map (leftApp F Y)) ≪≫
      Bicategory.whiskerLeftIso q (leftApp.mapIso F Y) ≪⊗≫
      Bicategory.whiskerLeftIso (eX.hom ≫ F.map f) eY.counit ≪≫
      ρ_ (eX.hom ≫ F.map f)) ≪≫
    (F.mapComp (leftApp F X) f ≪≫
      Bicategory.whiskerRightIso (leftApp.mapIso F X) (F.map f)).symm

/-- Naturality of the source-side comparison, obtained by lifting the explicit
image isomorphism through local full faithfulness. -/
noncomputable def leftNaturalityIso (F : B ⥤ᵖ C) [F.IsBiequivalence]
    {X Y : B} (f : X ⟶ Y) :
    (F.comp F.chosenInverse).map f ≫ leftApp F Y ≅ leftApp F X ≫ f :=
  (F.mapFunctor (F.objPreimage (F.obj X)) Y).preimageIso
    (leftNaturalityImageIso F f)

/-- The source-side comparison from `F` followed by its chosen pseudoinverse
to the identity pseudofunctor. -/
noncomputable def leftStrongTrans (F : B ⥤ᵖ C) [F.IsBiequivalence] :
    F.comp F.chosenInverse ⟶ Pseudofunctor.id B where
  app := leftApp F
  naturality := leftNaturalityIso F
  naturality_naturality := sorry
  naturality_id := sorry
  naturality_comp := sorry

/-- Pointwise equivalence data on the source-side comparison. -/
noncomputable def leftPointwise (F : B ⥤ᵖ C) [F.IsBiequivalence] :
    StrongTrans.PointwiseEquivalence (leftStrongTrans F) :=
  StrongTrans.PointwiseEquivalence.ofComponents
    (leftAppEquivalence F) (fun _ ↦ Iso.refl _)

/-- The source-side equivalence from `F` followed by its chosen pseudoinverse
to the identity pseudofunctor. -/
noncomputable def leftEquivalence (F : B ⥤ᵖ C) [F.IsBiequivalence] :
    F.comp F.chosenInverse ≌ Pseudofunctor.id B :=
  (leftPointwise F).toEquivalence

end ChosenInverse

end CategoryTheory.Pseudofunctor
