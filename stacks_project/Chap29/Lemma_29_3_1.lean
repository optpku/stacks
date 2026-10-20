/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.3.1 (1): if `Z ⟶ X` is an immersion, then `Z ⟶ Y` is an immersion. -/
@[stacks 07RK] #check
  (AlgebraicGeometry.IsImmersion.of_comp :
    ∀ {Z Y X : AlgebraicGeometry.Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
      [AlgebraicGeometry.IsImmersion (f ≫ g)], AlgebraicGeometry.IsImmersion f)

/- Lemma 29.3.1 (2): if `Z ⟶ X` is a quasi-compact immersion and `Y ⟶ X` is quasi-separated,
then `Z ⟶ Y` is a quasi-compact immersion. The check in clause (1) supplies the immersion
component, while this check supplies quasi-compactness. -/
@[stacks 07RK] #check
  (AlgebraicGeometry.QuasiCompact.of_comp :
    ∀ {Z Y X : AlgebraicGeometry.Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
      [AlgebraicGeometry.QuasiCompact (f ≫ g)] [AlgebraicGeometry.QuasiSeparated g],
      AlgebraicGeometry.QuasiCompact f)

/- Lemma 29.3.1 (3): if `Z ⟶ X` is a closed immersion and `Y ⟶ X` is separated, then `Z ⟶ Y` is
a closed immersion. -/
@[stacks 07RK] #check
  (AlgebraicGeometry.IsClosedImmersion.of_comp :
    ∀ {Z Y X : AlgebraicGeometry.Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
      [AlgebraicGeometry.IsClosedImmersion (f ≫ g)] [AlgebraicGeometry.IsSeparated g],
      AlgebraicGeometry.IsClosedImmersion f)
