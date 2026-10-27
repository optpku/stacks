/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationRestriction
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose

/-! # Small étale sheaves along closed immersions of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A sheaf of sets on `X_étale` restricts to the terminal sheaf `*` on the open
complement `X \ Z` of a closed immersion `i : Z ⟶ X`. -/
def restrictsToTerminalOnComplement {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) : Prop :=
  Nonempty
    ((etaleRestrictionSheaf (closedImmersionComplementι i) (Type (u + 1))).obj F ≅
      ⊤_ (Sheaf (smallEtaleTopology (closedImmersionComplement i)) (Type (u + 1))))

/-- Restriction to `X \ Z` is isomorphic to `*` if and only if the restricted sheaf is
terminal. -/
theorem restrictsToTerminalOnComplement_iff {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    restrictsToTerminalOnComplement i F ↔
      Nonempty
        (IsTerminal
          ((etaleRestrictionSheaf (closedImmersionComplementι i) (Type (u + 1))).obj F)) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨IsTerminal.ofIso terminalIsTerminal e.symm⟩
  · rintro ⟨h⟩
    exact ⟨h.uniqueUpToIso terminalIsTerminal⟩

/-- An abelian sheaf on `X_étale` has support contained in `|Z|` when every geometric
point at which the inverse-image sections over `Spec(k)` are nonzero lies in the image
of `|Z|`. -/
def supportSubsetImage {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    [∀ (xbar : GeometricPoint X) (G : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (etaleBaseChange xbar.hom).op.HasLeftKanExtension G]
    [∀ xbar : GeometricPoint X,
      HasWeakSheafify (spacesEtaleTopology (ofOver xbar.toFieldValuedPoint.overObj))
        AddCommGrpCat.{u + 1}]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) : Prop :=
  ∀ xbar : GeometricPoint X,
    IsZero
        (((sheafInverseImage AddCommGrpCat.{u + 1} xbar.hom).obj F).obj.obj
          (op xbar.toFieldValuedPoint.sourceObj)) ∨
      xbar.image ∈ pointsImage i

/-- Support contained in `|Z|` means that a geometric point with nonzero inverse-image
sections over `Spec(k)` has image in `|Z|`. -/
theorem supportSubsetImage_iff {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    [∀ (xbar : GeometricPoint X) (G : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (etaleBaseChange xbar.hom).op.HasLeftKanExtension G]
    [∀ xbar : GeometricPoint X,
      HasWeakSheafify (spacesEtaleTopology (ofOver xbar.toFieldValuedPoint.overObj))
        AddCommGrpCat.{u + 1}]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    supportSubsetImage i F ↔
      ∀ xbar : GeometricPoint X,
        ¬ IsZero
            (((sheafInverseImage AddCommGrpCat.{u + 1} xbar.hom).obj F).obj.obj
              (op xbar.toFieldValuedPoint.sourceObj)) →
          xbar.image ∈ pointsImage i := by
  classical
  constructor
  · intro h xbar hn
    exact (h xbar).resolve_left hn
  · intro h xbar
    by_cases hz : IsZero
        (((sheafInverseImage AddCommGrpCat.{u + 1} xbar.hom).obj F).obj.obj
          (op xbar.toFieldValuedPoint.sourceObj))
    · exact Or.inl hz
    · exact Or.inr (h xbar hz)

variable {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Small étale pushforward of sheaves of sets along a closed
immersion of algebraic spaces is full. -/
@[instance]
theorem sheafPushforward_closedImmersion_type_full :
    (sheafPushforward (Type (u + 1)) i).Full := sorry

/-- Small étale pushforward of sheaves of sets along a closed
immersion of algebraic spaces is faithful. -/
@[instance]
theorem sheafPushforward_closedImmersion_type_faithful :
    (sheafPushforward (Type (u + 1)) i).Faithful := sorry

/-- The essential image of small étale set-valued pushforward
along a closed immersion consists of sheaves whose restriction to `X \ Z` is isomorphic
to the terminal sheaf `*`. -/
theorem mem_essImage_sheafPushforward_closedImmersion_type_iff
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (sheafPushforward (Type (u + 1)) i).essImage F ↔
      restrictsToTerminalOnComplement i F := sorry

/-- Small étale inverse image of sheaves of sets is a left inverse
of pushforward along a closed immersion, equivalently the adjunction counit is invertible. -/
@[instance]
theorem isIso_counit_sheafPushforward_closedImmersion_type
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (etaleBaseChange i).op.HasLeftKanExtension P]
    [HasWeakSheafify (spacesEtaleTopology Z) (Type (u + 1))] :
    IsIso (sheafAdjunction (Type (u + 1)) i).counit :=
  (sheafAdjunction (Type (u + 1)) i).counit_isIso_of_R_fully_faithful

/-- Small étale pushforward of abelian sheaves along a closed
immersion of algebraic spaces is full. -/
@[instance]
theorem sheafPushforward_closedImmersion_ab_full :
    (sheafPushforward AddCommGrpCat.{u + 1} i).Full := sorry

/-- Small étale pushforward of abelian sheaves along a closed
immersion of algebraic spaces is faithful. -/
@[instance]
theorem sheafPushforward_closedImmersion_ab_faithful :
    (sheafPushforward AddCommGrpCat.{u + 1} i).Faithful := by
  let forgetX := sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u + 1})
  let forgetZ := sheafCompose (smallEtaleTopology Z) (forget AddCommGrpCat.{u + 1})
  let forgetSpaces := sheafCompose (spacesEtaleTopology Z) (forget AddCommGrpCat.{u + 1})
  let extendAb := (smallEtaleToSpaces Z).sheafPushforwardCocontinuous
    AddCommGrpCat.{u + 1} (smallEtaleTopology Z) (spacesEtaleTopology Z)
  let extendType := (smallEtaleToSpaces Z).sheafPushforwardCocontinuous
    (Type (u + 1)) (smallEtaleTopology Z) (spacesEtaleTopology Z)
  let evaluateAb := (etaleBaseChange i).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (smallEtaleTopology X) (spacesEtaleTopology Z)
  let evaluateType := (etaleBaseChange i).sheafPushforwardContinuous
    (Type (u + 1)) (smallEtaleTopology X) (spacesEtaleTopology Z)
  apply Functor.Faithful.of_comp_iso (G := forgetX)
    (H := forgetZ ⋙ sheafPushforward (Type (u + 1)) i)
  change (extendAb ⋙ evaluateAb) ⋙ forgetX ≅ forgetZ ⋙ (extendType ⋙ evaluateType)
  calc
    (extendAb ⋙ evaluateAb) ⋙ forgetX ≅ extendAb ⋙ (evaluateAb ⋙ forgetX) :=
      Functor.associator _ _ _
    _ ≅ extendAb ⋙ (forgetSpaces ⋙ evaluateType) := Iso.refl _
    _ ≅ (extendAb ⋙ forgetSpaces) ⋙ evaluateType := (Functor.associator _ _ _).symm
    _ ≅ (forgetZ ⋙ extendType) ⋙ evaluateType :=
      Functor.isoWhiskerRight
        (Functor.sheafPushforwardCocontinuous.compSheafComposeIso
          (smallEtaleToSpaces Z) (forget AddCommGrpCat.{u + 1})
          (smallEtaleTopology Z) (spacesEtaleTopology Z)) _
    _ ≅ forgetZ ⋙ (extendType ⋙ evaluateType) := Functor.associator _ _ _

/-- The essential image of small étale abelian pushforward along
a closed immersion consists of abelian sheaves whose support is contained in `|Z|`. -/
theorem mem_essImage_sheafPushforward_closedImmersion_ab_iff
    [∀ (xbar : GeometricPoint X) (G : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (etaleBaseChange xbar.hom).op.HasLeftKanExtension G]
    [∀ xbar : GeometricPoint X,
      HasWeakSheafify (spacesEtaleTopology (ofOver xbar.toFieldValuedPoint.overObj)) AddCommGrpCat.{u + 1}]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (sheafPushforward AddCommGrpCat.{u + 1} i).essImage F ↔
      supportSubsetImage i F := sorry

/-- Small étale inverse image of abelian sheaves is a left inverse
of pushforward along a closed immersion, equivalently the adjunction counit is invertible. -/
@[instance]
theorem isIso_counit_sheafPushforward_closedImmersion_ab
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleBaseChange i).op.HasLeftKanExtension P]
    [HasWeakSheafify (spacesEtaleTopology Z) AddCommGrpCat.{u + 1}] :
    IsIso (sheafAdjunction AddCommGrpCat.{u + 1} i).counit :=
  (sheafAdjunction AddCommGrpCat.{u + 1} i).counit_isIso_of_R_fully_faithful

end AlgebraicGeometry.AlgebraicSpace
