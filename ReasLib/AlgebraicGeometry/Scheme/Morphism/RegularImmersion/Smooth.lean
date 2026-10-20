/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion

import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.BaseChange
import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Composition
import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Implications
import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Section
import ReasLib.CategoryTheory.Limits.Shapes.Pullback.Graph

/-!
# Regular immersions over smooth morphisms

This module contains results transferring regularity of immersions in either direction along
commutative triangles whose second morphism is smooth.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- In a commutative triangle over a smooth morphism, a regular composite makes the first
morphism a regular immersion. -/
theorem isRegularImmersion_of_isRegularImmersion_over_smooth
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
    [IsImmersion i] [Smooth f] [IsRegularImmersion j] (hcomm : i ≫ f = j) :
    IsRegularImmersion i := sorry

/-- In a commutative triangle over a smooth morphism, a Koszul-regular composite makes the
first morphism a Koszul-regular immersion. -/
theorem isKoszulRegularImmersion_of_isKoszulRegularImmersion_over_smooth
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
    [IsImmersion i] [Smooth f] [IsKoszulRegularImmersion j] (hcomm : i ≫ f = j) :
    IsKoszulRegularImmersion i := sorry

/-- In a commutative triangle over a smooth morphism, an `H₁`-regular composite makes the
first morphism an `H₁`-regular immersion. -/
theorem isH1RegularImmersion_of_isH1RegularImmersion_over_smooth
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
    [IsImmersion i] [Smooth f] [IsH1RegularImmersion j] (hcomm : i ≫ f = j) :
    IsH1RegularImmersion i := sorry

/-- In a commutative triangle over a smooth morphism, a quasi-regular composite makes the
first morphism a quasi-regular immersion. -/
theorem isQuasiRegularImmersion_of_isQuasiRegularImmersion_over_smooth
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
    [IsImmersion i] [Smooth f] [IsQuasiRegularImmersion j] (hcomm : i ≫ f = j) :
    IsQuasiRegularImmersion i := sorry

/-- In a commutative triangle, postcomposition with a smooth morphism preserves
Koszul-regularity when the composite is an immersion. -/
theorem isKoszulRegularImmersion_of_isKoszulRegularImmersion_comp_smooth
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
    [IsImmersion j] [Smooth f] [IsKoszulRegularImmersion i] (hcomm : i ≫ f = j) :
    IsKoszulRegularImmersion j := sorry

/-- In a commutative triangle, postcomposition with a smooth morphism preserves
`H₁`-regularity when the composite is an immersion. -/
theorem isH1RegularImmersion_of_isH1RegularImmersion_comp_smooth
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
    [IsImmersion j] [Smooth f] [IsH1RegularImmersion i] (hcomm : i ≫ f = j) :
    IsH1RegularImmersion j := sorry

/-- In a commutative triangle, postcomposition with a smooth morphism preserves
quasi-regularity when the composite is an immersion. -/
theorem isQuasiRegularImmersion_of_isQuasiRegularImmersion_comp_smooth
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
    [IsImmersion j] [Smooth f] [IsQuasiRegularImmersion i] (hcomm : i ≫ f = j) :
    IsQuasiRegularImmersion j := sorry

end AlgebraicGeometry
