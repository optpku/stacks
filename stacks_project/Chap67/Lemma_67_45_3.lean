module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_45_3_Local

/-!
# Characterizations of integral and finite morphisms of algebraic spaces

Lemma 67.45.3 records that a morphism of algebraic spaces is integral,
respectively finite, iff it is representable and integral, respectively finite,
in the Section 67.3 sense, iff this is tested on a surjective étale scheme
atlas of the target, and iff this is tested on a Zariski covering of the
target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsIntegralHom

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 67.45.3 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is representable
and integral; `f` is integral; there exists a scheme `V` and a surjective étale
morphism `V ⟶ Y` such that `V ×_Y X ⟶ V` is integral; and there exists a
Zariski covering `Y = ⋃ Yᵢ` such that each of the morphisms `f⁻¹(Yᵢ) ⟶ Yᵢ` is
integral. -/
@[stacks 03ZQ]
theorem tfae :
    List.TFAE
      [ (over (@AlgebraicGeometry.IsIntegralHom :
          MorphismProperty Scheme.{u})).presheaf f
      , IsIntegralHom f
      , existsSurjectiveEtaleTarget f
      , existsZariskiCover f ] := sorry

/-- A morphism of algebraic spaces is integral iff it is representable and
integral in the sense of Section 67.3. -/
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

/-- Lemma 67.45.3 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is representable
and finite; `f` is finite; there exists a scheme `V` and a surjective étale
morphism `V ⟶ Y` such that `V ×_Y X ⟶ V` is finite; and there exists a Zariski
covering `Y = ⋃ Yᵢ` such that each of the morphisms `f⁻¹(Yᵢ) ⟶ Yᵢ` is finite. -/
@[stacks 03ZQ]
theorem tfae :
    List.TFAE
      [ (over (@AlgebraicGeometry.IsFinite :
          MorphismProperty Scheme.{u})).presheaf f
      , IsFinite f
      , existsSurjectiveEtaleTarget f
      , existsZariskiCover f ] := sorry

/-- A morphism of algebraic spaces is finite iff it is representable and finite
in the sense of Section 67.3. -/
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
