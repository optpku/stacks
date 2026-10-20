/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale.Small

variable {R : CommRingCat} [hR : Fact (IsField R)] (V : (Spec R).Etale)

include hR
variable [HasSheafify (Spec R).smallEtaleTopology AddCommGrpCat.{u}]

/-- A residue-field point of an étale scheme over a field is an open immersion. -/
theorem residuePoint_isOpenImmersion (point : V.left) :
    IsOpenImmersion (V.left.fromSpecResidueField point) := sorry

/-- The étale object over `Spec K` represented by the residue field at `point`. -/
noncomputable def residuePointObject (point : V.left) : (Spec R).Etale :=
  -- Local instance justification (proof-local temporary data): expose this field-specific open immersion to compose its étale structure with V.hom.
  letI : IsOpenImmersion (V.left.fromSpecResidueField point) :=
    residuePoint_isOpenImmersion V point
  Etale.mk (V.left.fromSpecResidueField point ≫ V.hom)

/-- The canonical arrow from a residue-point object back to the original étale object. -/
noncomputable def residuePointInclusion (point : V.left) :
    residuePointObject V point ⟶ V :=
  MorphismProperty.Over.homMk (V.left.fromSpecResidueField point) (by
    dsimp [residuePointObject]
    rfl)

/-- The residue-point arrows form a covering family in the small étale topology. -/
theorem residuePointCover :
    Sieve.ofArrows (fun point : V.left => residuePointObject V point)
        (residuePointInclusion V) ∈
      (Spec R).smallEtaleTopology V := sorry

/-- Evaluation of a function-valued section at a residue-point object. -/
private def pointValue (point : V.left) :
    AddCommGrpCat.of (V.left → ULift.{u} ℤ) ⟶
      ((constantSheaf (Spec R).smallEtaleTopology
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))).1.obj
        (op (residuePointObject V point)) :=
  AddCommGrpCat.ofHom
      (Pi.evalAddMonoidHom (fun _ : V.left => ULift.{u} ℤ) point) ≫
    (toSheafify (Spec R).smallEtaleTopology
        ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app
      (op (residuePointObject V point))

/-- Evaluations at residue points agree on every overlap above the base object. -/
private theorem pointValuesCompatible :
    ∀ ⦃W : (Spec R).Etale⦄ ⦃p q : V.left⦄
      (a : W ⟶ residuePointObject V p) (b : W ⟶ residuePointObject V q),
      a ≫ residuePointInclusion V p = b ≫ residuePointInclusion V q →
        pointValue V p ≫
            ((constantSheaf (Spec R).smallEtaleTopology
                AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))).1.map a.op =
          pointValue V q ≫
            ((constantSheaf (Spec R).smallEtaleTopology
                AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))).1.map b.op := sorry

/-- The constant-sheaf section with prescribed value at every geometric point. -/
@[no_expose]
noncomputable def pointwiseConstantSection :
    AddCommGrpCat.of (V.left → ULift.{u} ℤ) ⟶
      ((constantSheaf (Spec R).smallEtaleTopology
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))).1.obj (op V) :=
  CategoryTheory.Presheaf.IsSheaf.amalgamateOfArrows
      ((constantSheaf (Spec R).smallEtaleTopology
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))).property
      (residuePointInclusion V) (residuePointCover V)
      (pointValue V)
      (fun {W p q} a b h => pointValuesCompatible V a b h)

/-- Restriction of a pointwise constant section to a residue point is evaluation. -/
theorem pointwiseConstantSection_restrict (point : V.left)
    :
    pointwiseConstantSection V ≫
        ((constantSheaf (Spec R).smallEtaleTopology
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))).1.map
          (residuePointInclusion V point).op =
      AddCommGrpCat.ofHom
          (Pi.evalAddMonoidHom (fun _ : V.left => ULift.{u} ℤ) point) ≫
        (toSheafify (Spec R).smallEtaleTopology
          ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app
            (op (residuePointObject V point)) := sorry

/-- Pointwise constant sections are natural under pullback of étale objects. -/
theorem pointwiseConstantSection_naturality
    {W : (Spec R).Etale} (f : V ⟶ W)
    :
    pointwiseConstantSection W ≫
      ((constantSheaf (Spec R).smallEtaleTopology
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))).1.map f.op =
      AddCommGrpCat.ofHom (AddMonoidHom.mk'
          (fun (values : W.left → ULift.{u} ℤ) (point : V.left) =>
            values (f.left point)) (by
              intro values₁ values₂
              rfl)) ≫
        pointwiseConstantSection V := sorry

end AlgebraicGeometry.Scheme.Etale.Small
