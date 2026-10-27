/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Gorenstein
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Gorenstein residue-field fibres

Residue-field fibres can be tested after étale scheme base change on the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The residue-field fibres of a morphism from an algebraic space to a scheme
`V` over `S` are Gorenstein algebraic spaces. -/
def residueFibersIsGorenstein {S : Scheme.{u}} {X : AlgebraicSpace S}
    {V : Over S} (g : X ⟶ ofOver V) : Prop :=
  ∀ v : V.left, IsGorenstein (residueFiberOver g (𝟙 (ofOver V)) v)

/-- Residue-field fibres of `g : X ⟶ ofOver V` are Gorenstein if and only if
each residue-field fibre over a point of `V` is a Gorenstein algebraic space. -/
theorem residueFibersIsGorenstein_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {V : Over S} (g : X ⟶ ofOver V) :
    residueFibersIsGorenstein g ↔
      ∀ v : V.left, IsGorenstein (residueFiberOver g (𝟙 (ofOver V)) v) :=
  Iff.rfl

namespace Gorenstein

/-- There is a surjective étale morphism from a scheme to `Y` along which the
residue-field fibres of the base change of `f` are Gorenstein algebraic
spaces. -/
def existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (V : Over S) (b : ofOver V ⟶ Y),
    (over (@AlgebraicGeometry.Etale)).presheaf b ∧
      Surjective b ∧ residueFibersIsGorenstein (pullbackAlongScheme.snd f b)

/-- `existsSurjectiveEtaleTarget f` unpacks as a surjective étale scheme chart of
`Y` whose pullback has Gorenstein residue-field fibres. -/
theorem existsSurjectiveEtaleTarget_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    existsSurjectiveEtaleTarget f ↔
      ∃ (V : Over S) (b : ofOver V ⟶ Y),
        (over (@AlgebraicGeometry.Etale)).presheaf b ∧
          Surjective b ∧ residueFibersIsGorenstein (pullbackAlongScheme.snd f b) :=
  Iff.rfl

namespace existsSurjectiveEtaleTarget

/-- A surjective étale scheme chart of `Y` whose pullback has Gorenstein
residue-field fibres witnesses `existsSurjectiveEtaleTarget f`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {V : Over S}
    (b : ofOver V ⟶ Y) (hb_etale : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (hb_surj : Surjective b)
    (hfib : residueFibersIsGorenstein (pullbackAlongScheme.snd f b)) :
    existsSurjectiveEtaleTarget f :=
  ⟨V, b, hb_etale, hb_surj, hfib⟩

/-- `existsSurjectiveEtaleTarget f` supplies a surjective étale scheme chart of
`Y` whose pullback has Gorenstein residue-field fibres. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : existsSurjectiveEtaleTarget f) :
    ∃ (V : Over S) (b : ofOver V ⟶ Y),
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        Surjective b ∧ residueFibersIsGorenstein (pullbackAlongScheme.snd f b) :=
  h

end existsSurjectiveEtaleTarget

/-- For every étale morphism from a scheme to `Y`, the residue-field fibres of
the base change of `f` are Gorenstein algebraic spaces. -/
def forallEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ (V : Over S) (b : ofOver V ⟶ Y),
    (over (@AlgebraicGeometry.Etale)).presheaf b →
      residueFibersIsGorenstein (pullbackAlongScheme.snd f b)

/-- `forallEtaleTarget f` unpacks as Gorenstein residue-field fibres after every
étale scheme base change of `f`. -/
theorem forallEtaleTarget_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    forallEtaleTarget f ↔
      ∀ (V : Over S) (b : ofOver V ⟶ Y),
        (over (@AlgebraicGeometry.Etale)).presheaf b →
          residueFibersIsGorenstein (pullbackAlongScheme.snd f b) :=
  Iff.rfl

namespace forallEtaleTarget

/-- The universal étale-scheme-base-change condition witnesses
`forallEtaleTarget f`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ (V : Over S) (b : ofOver V ⟶ Y),
      (over (@AlgebraicGeometry.Etale)).presheaf b →
        residueFibersIsGorenstein (pullbackAlongScheme.snd f b)) :
    forallEtaleTarget f :=
  h

/-- If `forallEtaleTarget f`, then every étale scheme base change of `f` has
Gorenstein residue-field fibres. -/
theorem apply {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : forallEtaleTarget f) {V : Over S} (b : ofOver V ⟶ Y)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b) :
    residueFibersIsGorenstein (pullbackAlongScheme.snd f b) :=
  hf V b hb

end forallEtaleTarget

end Gorenstein

end AlgebraicGeometry.AlgebraicSpace
