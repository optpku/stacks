/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat

/-! # Formal glueing of algebraic spaces along a closed immersion -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The formal-glueing conditions on `f : Y ⟶ X` and a finite-presentation
closed immersion `i : Z ⟶ X`: `inverseImageTo f i` is an isomorphism and `f` is flat at
every point of `pointsImage (inverseImageι f i)`. -/
class IsFormalGlueing {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i] : Prop where
  /-- The comparison `inverseImageTo f i` is an isomorphism. -/
  [inverseImageTo_isIso : IsIso (inverseImageTo f i)]
  /-- `f` is flat at every point of the inverse image of `i`. -/
  flatAt_inverseImage :
    ∀ x : Points Y, x ∈ pointsImage (inverseImageι f i) → FlatAt f x

namespace IsFormalGlueing

/-- Pack an isomorphism `inverseImageTo f i` together with pointwise flatness on
`pointsImage (inverseImageι f i)` into the formal-glueing predicate. -/
theorem of {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsIso (inverseImageTo f i)]
    (h : ∀ x : Points Y, x ∈ pointsImage (inverseImageι f i) → FlatAt f x) :
    IsFormalGlueing f i :=
  sorry

/-- Formal glueing is the conjunction of an isomorphism `inverseImageTo f i` and
pointwise flatness of `f` on `pointsImage (inverseImageι f i)`. -/
theorem iff {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i] :
    IsFormalGlueing f i ↔
      IsIso (inverseImageTo f i) ∧
        ∀ x : Points Y, x ∈ pointsImage (inverseImageι f i) → FlatAt f x :=
  sorry

/-- Formal glueing gives an isomorphic inverse-image comparison and pointwise flatness
along the inverse image. -/
theorem spec {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    IsIso (inverseImageTo f i) ∧
      ∀ x : Points Y, x ∈ pointsImage (inverseImageι f i) → FlatAt f x :=
  sorry

/-- Formal glueing implies flatness of `f` at every point of
`pointsImage (inverseImageι f i)`. -/
theorem flatAt {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] {x : Points Y}
    (hx : x ∈ pointsImage (inverseImageι f i)) : FlatAt f x :=
  sorry

/-- The identity on `X` is a formal-glueing morphism relative to any finite-presentation
closed immersion `i : Z ⟶ X`. -/
instance id {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] [FinitePresentation i] : IsFormalGlueing (𝟙 X) i :=
  sorry

/-- A globally flat morphism with isomorphic inverse image along `i` is a formal-glueing
morphism. -/
instance of_flat {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsIso (inverseImageTo f i)] [Flat f] : IsFormalGlueing f i :=
  sorry

end IsFormalGlueing

end AlgebraicGeometry.AlgebraicSpace
