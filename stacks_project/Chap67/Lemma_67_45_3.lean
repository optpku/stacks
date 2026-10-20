/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.IntegralFinite.Locality
import StacksCheckRecall

/-!
# Characterizations of integral and finite morphisms of algebraic spaces

Integrality and finiteness can be tested by representability, on a surjective
étale scheme atlas of the target, or on a Zariski covering of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.45.3 (1): the four characterizations of integral morphisms. -/
@[stacks 03ZQ] #check (AlgebraicGeometry.AlgebraicSpace.IsIntegralHom.tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE
      [ (over (@AlgebraicGeometry.IsIntegralHom :
          MorphismProperty Scheme.{u})).presheaf f
      , IsIntegralHom f
      , IsIntegralHom.existsSurjectiveEtaleTarget f
      , IsIntegralHom.existsZariskiCover f ])

#check (AlgebraicGeometry.AlgebraicSpace.IsIntegralHom.iff_presheaf :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    IsIntegralHom f ↔
    (over (@AlgebraicGeometry.IsIntegralHom :
      MorphismProperty Scheme.{u})).presheaf f)

#check (AlgebraicGeometry.AlgebraicSpace.IsIntegralHom.iff_existsSurjectiveEtaleTarget :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    IsIntegralHom f ↔ IsIntegralHom.existsSurjectiveEtaleTarget f)

#check (AlgebraicGeometry.AlgebraicSpace.IsIntegralHom.iff_existsZariskiCover :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    IsIntegralHom f ↔ IsIntegralHom.existsZariskiCover f)

/- Lemma 67.45.3 (2): the four characterizations of finite morphisms. -/
@[stacks 03ZQ] #check (AlgebraicGeometry.AlgebraicSpace.IsFinite.tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE
      [ (over (@AlgebraicGeometry.IsFinite :
          MorphismProperty Scheme.{u})).presheaf f
      , IsFinite f
      , IsFinite.existsSurjectiveEtaleTarget f
      , IsFinite.existsZariskiCover f ])

#check (AlgebraicGeometry.AlgebraicSpace.IsFinite.iff_presheaf :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    IsFinite f ↔
    (over (@AlgebraicGeometry.IsFinite :
      MorphismProperty Scheme.{u})).presheaf f)

#check (AlgebraicGeometry.AlgebraicSpace.IsFinite.iff_existsSurjectiveEtaleTarget :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    IsFinite f ↔ IsFinite.existsSurjectiveEtaleTarget f)

#check (AlgebraicGeometry.AlgebraicSpace.IsFinite.iff_existsZariskiCover :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    IsFinite f ↔ IsFinite.existsZariskiCover f)

end AlgebraicGeometry.AlgebraicSpace
