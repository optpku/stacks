/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal

/-!
# Regular immersions of algebraic spaces

A representable morphism of algebraic spaces over a scheme `S` is a
Koszul-regular, `H₁`-regular, or quasi-regular immersion when the
corresponding scheme-morphism property is étale local on the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `i : X ⟶ Y` of algebraic spaces over `S` is a Koszul-regular
immersion if it is representable and every étale scheme pullback of `i` is a
Koszul-regular immersion of schemes. -/
class IsKoszulRegularImmersion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (i : X ⟶ Y) : Prop where
  /-- The morphism is representable by schemes. -/
  representable : yoneda.relativelyRepresentable i
  /-- Every étale scheme pullback of `i` is a Koszul-regular immersion of
  schemes. -/
  etaleLocal : etaleLocalOnTarget
    (fun _ _ f ↦ AlgebraicGeometry.IsKoszulRegularImmersion f) i

/-- A morphism `i : X ⟶ Y` of algebraic spaces over `S` is an `H₁`-regular
immersion if it is representable and every étale scheme pullback of `i` is an
`H₁`-regular immersion of schemes. -/
class IsH1RegularImmersion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (i : X ⟶ Y) : Prop where
  /-- The morphism is representable by schemes. -/
  representable : yoneda.relativelyRepresentable i
  /-- Every étale scheme pullback of `i` is an `H₁`-regular immersion of
  schemes. -/
  etaleLocal : etaleLocalOnTarget
    (fun _ _ f ↦ AlgebraicGeometry.IsH1RegularImmersion f) i

/-- A morphism `i : X ⟶ Y` of algebraic spaces over `S` is a quasi-regular
immersion if it is representable and every étale scheme pullback of `i` is a
quasi-regular immersion of schemes. -/
class IsQuasiRegularImmersion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (i : X ⟶ Y) : Prop where
  /-- The morphism is representable by schemes. -/
  representable : yoneda.relativelyRepresentable i
  /-- Every étale scheme pullback of `i` is a quasi-regular immersion of
  schemes. -/
  etaleLocal : etaleLocalOnTarget
    (fun _ _ f ↦ AlgebraicGeometry.IsQuasiRegularImmersion f) i

/-- A morphism of algebraic spaces is a Koszul-regular immersion iff it is
representable and every étale scheme pullback is a Koszul-regular immersion of
schemes. -/
theorem isKoszulRegularImmersion_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (i : X ⟶ Y) :
    IsKoszulRegularImmersion i ↔
      yoneda.relativelyRepresentable i ∧
        etaleLocalOnTarget
          (fun _ _ f ↦ AlgebraicGeometry.IsKoszulRegularImmersion f) i :=
  sorry

/-- A morphism of algebraic spaces is an `H₁`-regular immersion iff it is
representable and every étale scheme pullback is an `H₁`-regular immersion of
schemes. -/
theorem isH1RegularImmersion_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (i : X ⟶ Y) :
    IsH1RegularImmersion i ↔
      yoneda.relativelyRepresentable i ∧
        etaleLocalOnTarget
          (fun _ _ f ↦ AlgebraicGeometry.IsH1RegularImmersion f) i :=
  sorry

/-- A morphism of algebraic spaces is a quasi-regular immersion iff it is
representable and every étale scheme pullback is a quasi-regular immersion of
schemes. -/
theorem isQuasiRegularImmersion_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (i : X ⟶ Y) :
    IsQuasiRegularImmersion i ↔
      yoneda.relativelyRepresentable i ∧
        etaleLocalOnTarget
          (fun _ _ f ↦ AlgebraicGeometry.IsQuasiRegularImmersion f) i :=
  sorry

namespace IsKoszulRegularImmersion

/-- A Koszul-regular immersion of algebraic spaces is representable, and every
étale scheme pullback is a Koszul-regular immersion of schemes. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (i : X ⟶ Y)
    [IsKoszulRegularImmersion i] :
    yoneda.relativelyRepresentable i ∧
      etaleLocalOnTarget
        (fun _ _ f ↦ AlgebraicGeometry.IsKoszulRegularImmersion f) i :=
  sorry

/-- A Koszul-regular immersion of algebraic spaces is representable. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (i : X ⟶ Y) [IsKoszulRegularImmersion i] :
    yoneda.relativelyRepresentable i :=
  sorry

/-- The identity morphism of an algebraic space is a Koszul-regular immersion. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsKoszulRegularImmersion (𝟙 X) :=
  sorry

/-- The étale pullback condition for a Koszul-regular immersion implies the
relative immersion property on the induced morphism of functors of points. -/
theorem immersionPresheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (i : X ⟶ Y) [IsKoszulRegularImmersion i] :
    (MorphismProperty.over (@AlgebraicGeometry.IsImmersion :
      MorphismProperty Scheme.{u})).presheaf i :=
  sorry

end IsKoszulRegularImmersion

namespace IsH1RegularImmersion

/-- An `H₁`-regular immersion of algebraic spaces is representable, and every
étale scheme pullback is an `H₁`-regular immersion of schemes. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (i : X ⟶ Y)
    [IsH1RegularImmersion i] :
    yoneda.relativelyRepresentable i ∧
      etaleLocalOnTarget
        (fun _ _ f ↦ AlgebraicGeometry.IsH1RegularImmersion f) i :=
  sorry

/-- An `H₁`-regular immersion of algebraic spaces is representable. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (i : X ⟶ Y) [IsH1RegularImmersion i] :
    yoneda.relativelyRepresentable i :=
  sorry

/-- The identity morphism of an algebraic space is an `H₁`-regular immersion. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsH1RegularImmersion (𝟙 X) :=
  sorry

/-- The étale pullback condition for an `H₁`-regular immersion implies the
relative immersion property on the induced morphism of functors of points. -/
theorem immersionPresheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (i : X ⟶ Y) [IsH1RegularImmersion i] :
    (MorphismProperty.over (@AlgebraicGeometry.IsImmersion :
      MorphismProperty Scheme.{u})).presheaf i :=
  sorry

end IsH1RegularImmersion

namespace IsQuasiRegularImmersion

/-- A quasi-regular immersion of algebraic spaces is representable, and every
étale scheme pullback is a quasi-regular immersion of schemes. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (i : X ⟶ Y)
    [IsQuasiRegularImmersion i] :
    yoneda.relativelyRepresentable i ∧
      etaleLocalOnTarget
        (fun _ _ f ↦ AlgebraicGeometry.IsQuasiRegularImmersion f) i :=
  sorry

/-- A quasi-regular immersion of algebraic spaces is representable. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (i : X ⟶ Y) [IsQuasiRegularImmersion i] :
    yoneda.relativelyRepresentable i :=
  sorry

/-- The identity morphism of an algebraic space is a quasi-regular immersion. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsQuasiRegularImmersion (𝟙 X) :=
  sorry

/-- The étale pullback condition for a quasi-regular immersion implies the
relative immersion property on the induced morphism of functors of points. -/
theorem immersionPresheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (i : X ⟶ Y) [IsQuasiRegularImmersion i] :
    (MorphismProperty.over (@AlgebraicGeometry.IsImmersion :
      MorphismProperty Scheme.{u})).presheaf i :=
  sorry

end IsQuasiRegularImmersion

/-- A morphism of algebraic spaces is a Koszul-regular immersion iff it is
representable and some surjective étale scheme pullback is a Koszul-regular
immersion of schemes. -/
theorem isKoszulRegularImmersion_iff_existsSurjectivePullback
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (i : X ⟶ Y) :
    IsKoszulRegularImmersion i ↔
      yoneda.relativelyRepresentable i ∧
        etaleLocalOnTarget.existsSurjectivePullback
          (fun _ _ f ↦ AlgebraicGeometry.IsKoszulRegularImmersion f) i :=
  sorry

/-- A morphism of algebraic spaces is an `H₁`-regular immersion iff it is
representable and some surjective étale scheme pullback is an `H₁`-regular
immersion of schemes. -/
theorem isH1RegularImmersion_iff_existsSurjectivePullback
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (i : X ⟶ Y) :
    IsH1RegularImmersion i ↔
      yoneda.relativelyRepresentable i ∧
        etaleLocalOnTarget.existsSurjectivePullback
          (fun _ _ f ↦ AlgebraicGeometry.IsH1RegularImmersion f) i :=
  sorry

/-- A morphism of algebraic spaces is a quasi-regular immersion iff it is
representable and some surjective étale scheme pullback is a quasi-regular
immersion of schemes. -/
theorem isQuasiRegularImmersion_iff_existsSurjectivePullback
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (i : X ⟶ Y) :
    IsQuasiRegularImmersion i ↔
      yoneda.relativelyRepresentable i ∧
        etaleLocalOnTarget.existsSurjectivePullback
          (fun _ _ f ↦ AlgebraicGeometry.IsQuasiRegularImmersion f) i :=
  sorry

/-- The morphism of algebraic spaces induced by a morphism of schemes over `S`
is a Koszul-regular immersion iff the underlying scheme morphism is a
Koszul-regular immersion. -/
theorem isKoszulRegularImmersion_ofOverMap_iff {S : Scheme.{u}}
    {U V : Over S} (h : U ⟶ V) :
    IsKoszulRegularImmersion (X := ofOver U) (Y := ofOver V) (yoneda.map h) ↔
      AlgebraicGeometry.IsKoszulRegularImmersion h.left :=
  sorry

/-- The morphism of algebraic spaces induced by a morphism of schemes over `S`
is an `H₁`-regular immersion iff the underlying scheme morphism is an
`H₁`-regular immersion. -/
theorem isH1RegularImmersion_ofOverMap_iff {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) :
    IsH1RegularImmersion (X := ofOver U) (Y := ofOver V) (yoneda.map h) ↔
      AlgebraicGeometry.IsH1RegularImmersion h.left :=
  sorry

/-- The morphism of algebraic spaces induced by a morphism of schemes over `S`
is a quasi-regular immersion iff the underlying scheme morphism is a
quasi-regular immersion. -/
theorem isQuasiRegularImmersion_ofOverMap_iff {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) :
    IsQuasiRegularImmersion (X := ofOver U) (Y := ofOver V) (yoneda.map h) ↔
      AlgebraicGeometry.IsQuasiRegularImmersion h.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
