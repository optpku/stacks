/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.IntegralFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic

/-!
# Locality of integral and finite morphisms of algebraic spaces

Integrality and finiteness are equivalent to their representable scheme-morphism
conditions and can be tested on a surjective étale scheme atlas or a Zariski
covering of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsIntegralHom

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- There is a surjective étale morphism from a scheme to `Y` along which every
pullback of `f` is integral. -/
def existsSurjectiveEtaleTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
        IsPullback pV pX ψ f → IsIntegralHom pV

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` is integral. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → IsIntegralHom pYi

/-- A morphism of algebraic spaces is representable and integral if and only if
it is integral, if and only if its pullbacks along a surjective étale scheme
atlas are integral, if and only if its pullbacks along a Zariski covering of
the target are integral. -/
theorem tfae :
    List.TFAE
      [ (over (@AlgebraicGeometry.IsIntegralHom :
          MorphismProperty Scheme.{u})).presheaf f
      , IsIntegralHom f
      , existsSurjectiveEtaleTarget f
      , existsZariskiCover f ] := sorry

/-- A morphism of algebraic spaces is integral iff it is representable and
integral as a scheme morphism after every scheme base change. -/
theorem iff_presheaf : IsIntegralHom f ↔
    (over (@AlgebraicGeometry.IsIntegralHom :
      MorphismProperty Scheme.{u})).presheaf f := sorry

/-- A morphism of algebraic spaces is integral iff some surjective étale scheme
atlas of the target has integral pullback. -/
theorem iff_existsSurjectiveEtaleTarget :
    IsIntegralHom f ↔ existsSurjectiveEtaleTarget f := sorry

/-- A morphism of algebraic spaces is integral iff some Zariski covering of the
target has integral inverse images under `f`. -/
theorem iff_existsZariskiCover : IsIntegralHom f ↔ existsZariskiCover f := sorry

end IsIntegralHom

namespace IsFinite

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- There is a surjective étale morphism from a scheme to `Y` along which every
pullback of `f` is finite. -/
def existsSurjectiveEtaleTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
        IsPullback pV pX ψ f → IsFinite pV

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` is finite. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → IsFinite pYi

/-- A morphism of algebraic spaces is representable and finite if and only if
it is finite, if and only if its pullbacks along a surjective étale scheme
atlas are finite, if and only if its pullbacks along a Zariski covering of
the target are finite. -/
theorem tfae :
    List.TFAE
      [ (over (@AlgebraicGeometry.IsFinite :
          MorphismProperty Scheme.{u})).presheaf f
      , IsFinite f
      , existsSurjectiveEtaleTarget f
      , existsZariskiCover f ] := sorry

/-- A morphism of algebraic spaces is finite iff it is representable and finite
as a scheme morphism after every scheme base change. -/
theorem iff_presheaf : IsFinite f ↔
    (over (@AlgebraicGeometry.IsFinite :
      MorphismProperty Scheme.{u})).presheaf f := sorry

/-- A morphism of algebraic spaces is finite iff some surjective étale scheme
atlas of the target has finite pullback. -/
theorem iff_existsSurjectiveEtaleTarget :
    IsFinite f ↔ existsSurjectiveEtaleTarget f := sorry

/-- A morphism of algebraic spaces is finite iff some Zariski covering of the
target has finite inverse images under `f`. -/
theorem iff_existsZariskiCover : IsFinite f ↔ existsZariskiCover f := sorry

end IsFinite

end AlgebraicGeometry.AlgebraicSpace
