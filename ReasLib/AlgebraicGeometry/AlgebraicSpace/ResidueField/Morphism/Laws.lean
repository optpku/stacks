/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField.Morphism
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Laws for residue-field maps

Residue-field maps preserve identities, compose contravariantly, and recover
the maps of spectra in residue-point factorizations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

open FieldValuedPoint

/-- The identity morphism induces the identity on residue fields. -/
theorem residueFieldMap_id {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X) :
    residueFieldMap (𝟙 X) x =
      eqToHom (congrArg X.residueField (Points.map_id x)) :=
  sorry

/-- Residue-field homomorphisms compose contravariantly. -/
theorem residueFieldMap_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] [IsDecent Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Points X) :
    residueFieldMap (f ≫ g) x =
      eqToHom (congrArg Z.residueField (Points.map_comp f g x)) ≫
        residueFieldMap g (Points.map f x) ≫ residueFieldMap f x :=
  sorry

/-- The spectrum of the induced residue-field map is the scheme morphism of
any factorization through the residue point of the image. -/
theorem specMap_residueFieldMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X)
    (φ : Factorization ((residuePoint x).map f)
      (residuePoint (Points.map f x))) :
    Spec.map (residueFieldMap f x) = φ.schemeHom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
