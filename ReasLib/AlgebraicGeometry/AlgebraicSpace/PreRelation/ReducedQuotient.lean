/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.CategoricalQuotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme

/-!
# Reducedness of categorical quotients
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- The target of a categorical quotient of a pre-relation on a reduced algebraic
space is reduced. -/
theorem IsCategoricalQuotient.isReduced {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) {φ : U ⟶ X}
    (hφ : P.IsCategoricalQuotient φ) [IsReduced U.left] : IsReduced X.left :=
  sorry

/-- The target of a categorical quotient in separated algebraic spaces over a
separated base is reduced if its source is reduced. -/
theorem IsCategoricalQuotientInSeparated.isReduced {S : Scheme.{u}}
    {B : AlgebraicSpace S} [IsAbsolutelySeparated B] {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X}
    (hφ : P.IsCategoricalQuotientIn (fun Y ↦ IsAbsolutelySeparated Y.left) φ)
    [IsReduced U.left] : IsReduced X.left :=
  sorry

/-- The target of a categorical quotient in quasi-separated algebraic spaces over a
quasi-separated base is reduced if its source is reduced. -/
theorem IsCategoricalQuotientInQuasiSeparated.isReduced {S : Scheme.{u}}
    {B : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated B] {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X}
    (hφ : P.IsCategoricalQuotientIn (fun Y ↦ IsAbsolutelyQuasiSeparated Y.left) φ)
    [IsReduced U.left] : IsReduced X.left :=
  sorry

/-- The target of a categorical quotient in locally separated algebraic spaces over a
locally separated base is reduced if its source is reduced. -/
theorem IsCategoricalQuotientInLocallySeparated.isReduced {S : Scheme.{u}}
    {B : AlgebraicSpace S} [IsAbsolutelyLocallySeparated B] {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X}
    (hφ : P.IsCategoricalQuotientIn (fun Y ↦ IsAbsolutelyLocallySeparated Y.left) φ)
    [IsReduced U.left] : IsReduced X.left :=
  sorry

/-- The target of a categorical quotient in decent algebraic spaces over a decent
base is reduced if its source is reduced. -/
theorem IsCategoricalQuotientInDecent.isReduced {S : Scheme.{u}}
    {B : AlgebraicSpace S} [IsDecent B] {U X : Over B} (P : PreRelation U)
    {φ : U ⟶ X} (hφ : P.IsCategoricalQuotientIn (fun Y ↦ IsDecent Y.left) φ)
    [IsReduced U.left] : IsReduced X.left :=
  sorry

/-- The target of a categorical quotient in schemes over a scheme is reduced if its
source is reduced. -/
theorem IsCategoricalQuotientInSchemes.isReduced {S : Scheme.{u}}
    {U X : Over (ofOver (Over.mk (𝟙 S)))} (P : PreRelation U) {φ : U ⟶ X}
    (hφ : P.IsCategoricalQuotientIn (fun Y ↦ IsScheme Y.left) φ)
    [IsReduced U.left] : IsReduced X.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
