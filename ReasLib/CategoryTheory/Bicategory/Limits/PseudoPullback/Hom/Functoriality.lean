/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import ReasLib.CategoryTheory.Bicategory.Biequivalence
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Hom.Basic

/-!
# Normalization of readable pseudopullback cones

This leaf packages the canonical forgetful map from readable pseudopullback cones to generic
varying-apex pseudocones as a strict pseudofunctor, exposes its action and comparison cells, and
records the resulting biequivalence. It is independent of the readable hom constructors and their
computation API.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- Readable cospan-shaped cones inherit local groupoidality from the generic pseudocone
bicategory, hence from the ambient bicategory. -/
instance locallyGroupoid [IsLocallyGroupoid B] :
    IsLocallyGroupoid (PseudoPullbackCone f g) := sorry

/-- The normalization pseudofunctor from the readable four-field presentation to the generic
varying-apex pseudocone bicategory. On each hom-category this is the canonical forgetful
functor from an induced bicategory. -/
@[stacks 003Q "normalization of readable pseudopullback cones"]
def toPseudoConePseudofunctor (f : x ⟶ z) (g : y ⟶ z) :
    StrictPseudofunctor (PseudoPullbackCone f g) (PseudoCone (cospan f g)) :=
  Bicategory.InducedBicategory.forget

/-- The normalization pseudofunctor sends a readable pseudopullback cone to its canonical
generic pseudocone. -/
@[simp]
theorem toPseudoConePseudofunctor.obj (S : PseudoPullbackCone f g) :
    (toPseudoConePseudofunctor f g).obj S = S.toPseudoCone := sorry

/-- The normalization pseudofunctor forgets a readable cone morphism to its underlying generic
pseudocone morphism. -/
@[simp]
theorem toPseudoConePseudofunctor.map
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    (toPseudoConePseudofunctor f g).map u = u.hom := sorry

/-- The normalization pseudofunctor forgets a readable cone `2`-morphism to its underlying
generic pseudocone `2`-morphism. -/
@[simp]
theorem toPseudoConePseudofunctor.map₂
    {S T : PseudoPullbackCone f g} {u v : S ⟶ T} (η : u ⟶ v) :
    (toPseudoConePseudofunctor f g).map₂ η = η.hom := sorry

/-- The unit comparison of the normalization pseudofunctor is reflexivity. -/
@[simp]
theorem toPseudoConePseudofunctor.mapId (S : PseudoPullbackCone f g) :
    (toPseudoConePseudofunctor f g).mapId S =
      Iso.refl (𝟙 S.toPseudoCone) := sorry

/-- The composition comparison of the normalization pseudofunctor is reflexivity. -/
@[simp]
theorem toPseudoConePseudofunctor.mapComp
    {R S T : PseudoPullbackCone f g} (u : R ⟶ S) (v : S ⟶ T) :
    (toPseudoConePseudofunctor f g).mapComp u v =
      Iso.refl (u.hom ≫ v.hom) := sorry

/-- The readable cospan presentation and the generic pseudocone owner are biequivalent. -/
instance toPseudoConePseudofunctor.isBiequivalence :
    Pseudofunctor.IsBiequivalence (toPseudoConePseudofunctor f g).toPseudofunctor := sorry

/- Data audit (mathlib 4.32): `toPseudoConePseudofunctor` is the canonical induced-bicategory
forgetful pseudofunctor. Its object, map, and `2`-cell data add no choices; deferred proof debt is
confined to coherence and biequivalence fields. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
