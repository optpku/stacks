/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange.Fppf
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat

/-! # Exact inverse image from étale to fppf modules -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.ObjectProperty
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Underived inverse image `ε^*` of module sheaves along `etaleFppfHom`. -/
abbrev etaleFppfInverseImage (X : GroupoidsOver S) :
    etaleModules X ⥤ fppfModules X :=
  (etaleFppfHom X).modulePullback.{u}

/-- The identity-on-objects comparison `ε : X_fppf ⟶ X_étale` is categorically
flat, so `ε^*` is exact on module sheaves. -/
instance etaleFppfHom_isFlat (X : GroupoidsOver S) [AlgebraicStack X] :
    IsFlat.{u} (etaleFppfHom X) := sorry

/-- Underived `ε^*` is additive. -/
instance etaleFppfInverseImage.instAdditive (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (etaleFppfInverseImage X).Additive :=
  modulePullback_additive (etaleFppfHom X)

/-- Bundled exact underived inverse image along `etaleFppfHom`. -/
abbrev etaleFppfInverseImageExact (X : GroupoidsOver S) [AlgebraicStack X] :
    etaleModules X ⥤ₑ fppfModules X :=
  IsFlat.exactPullback.{u} (etaleFppfHom X)

end AlgebraicGeometry.AlgebraicStack
