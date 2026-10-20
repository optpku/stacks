module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.TorIndependence
public import ReasLib.AlgebraicGeometry.Scheme.TorIndependence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Étale test diagrams for Tor independence

Tor independence of algebraic spaces over a common base is tested on commutative
diagrams with étale vertical arrows, including étale-surjective covers and
representable scheme atlases.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace TorIndependentOver

/-- A commutative diagram of algebraic spaces `U ⟶ W ⟵ V` over `X ⟶ B ⟵ Y` whose
vertical arrows `U ⟶ X`, `W ⟶ B`, and `V ⟶ Y` are étale. -/
structure EtaleDiagram {S : Scheme.{u}} {B : AlgebraicSpace S} (X Y : Over B) where
  /-- The algebraic space `U` mapping to `X` and `W`. -/
  U : AlgebraicSpace S
  /-- The algebraic space `V` mapping to `Y` and `W`. -/
  V : AlgebraicSpace S
  /-- The algebraic space `W` mapping to `B`. -/
  W : AlgebraicSpace S
  /-- The vertical morphism `U ⟶ X`. -/
  toX : U ⟶ X.left
  /-- The vertical morphism `V ⟶ Y`. -/
  toY : V ⟶ Y.left
  /-- The vertical morphism `W ⟶ B`. -/
  toB : W ⟶ B
  /-- The horizontal morphism `U ⟶ W`. -/
  fst : U ⟶ W
  /-- The horizontal morphism `V ⟶ W`. -/
  snd : V ⟶ W
  /-- The left square commutes. -/
  sqX : CommSq toX fst X.hom toB
  /-- The right square commutes. -/
  sqY : CommSq toY snd Y.hom toB
  /-- The morphism `U ⟶ X` is étale. -/
  etale_toX : Etale toX
  /-- The morphism `V ⟶ Y` is étale. -/
  etale_toY : Etale toY
  /-- The morphism `W ⟶ B` is étale. -/
  etale_toB : Etale toB

namespace EtaleDiagram

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {X Y : Over B}

/-- The induced morphism `U ⟶ X ×_B W` from the left commutative square. -/
def liftX (D : EtaleDiagram X Y) : D.U ⟶ pullback X.hom D.toB :=
  pullback.lift D.toX D.fst D.sqX.w

/-- The induced morphism `V ⟶ Y ×_B W` from the right commutative square. -/
def liftY (D : EtaleDiagram X Y) : D.V ⟶ pullback Y.hom D.toB :=
  pullback.lift D.toY D.snd D.sqY.w

/-- `liftX` recovers the vertical arrow `U ⟶ X`. -/
theorem liftX_fst (D : EtaleDiagram X Y) :
    D.liftX ≫ pullback.fst X.hom D.toB = D.toX := by
  exact pullback.lift_fst D.toX D.fst D.sqX.w

/-- `liftX` recovers the horizontal arrow `U ⟶ W`. -/
theorem liftX_snd (D : EtaleDiagram X Y) :
    D.liftX ≫ pullback.snd X.hom D.toB = D.fst := by
  exact pullback.lift_snd D.toX D.fst D.sqX.w

/-- `liftY` recovers the vertical arrow `V ⟶ Y`. -/
theorem liftY_fst (D : EtaleDiagram X Y) :
    D.liftY ≫ pullback.fst Y.hom D.toB = D.toY := by
  exact pullback.lift_fst D.toY D.snd D.sqY.w

/-- `liftY` recovers the horizontal arrow `V ⟶ W`. -/
theorem liftY_snd (D : EtaleDiagram X Y) :
    D.liftY ≫ pullback.snd Y.hom D.toB = D.snd := by
  exact pullback.lift_snd D.toY D.snd D.sqY.w

/-- `liftX` is the universal map `U ⟶ X ×_B W` induced by the left square. -/
theorem liftX_eq (D : EtaleDiagram X Y) :
    D.liftX = pullback.lift D.toX D.fst D.sqX.w :=
  rfl

/-- `liftY` is the universal map `V ⟶ Y ×_B W` induced by the right square. -/
theorem liftY_eq (D : EtaleDiagram X Y) :
    D.liftY = pullback.lift D.toY D.snd D.sqY.w :=
  rfl

/-- The maps `W ⟶ B`, `U ⟶ X ×_B W`, and `V ⟶ Y ×_B W` are étale surjective. -/
structure IsCover (D : EtaleDiagram X Y) : Prop where
  /-- The morphism `W ⟶ B` is surjective. -/
  surjective_toB : Surjective D.toB
  /-- The morphism `U ⟶ X ×_B W` is étale. -/
  etale_liftX : Etale D.liftX
  /-- The morphism `U ⟶ X ×_B W` is surjective. -/
  surjective_liftX : Surjective D.liftX
  /-- The morphism `V ⟶ Y ×_B W` is étale. -/
  etale_liftY : Etale D.liftY
  /-- The morphism `V ⟶ Y ×_B W` is surjective. -/
  surjective_liftY : Surjective D.liftY

/-- Package the étale-surjective covering conditions of a diagram. -/
def IsCover.of (D : EtaleDiagram X Y) (hB : Surjective D.toB) (hEtaleX : Etale D.liftX)
    (hSurjX : Surjective D.liftX) (hEtaleY : Etale D.liftY)
    (hSurjY : Surjective D.liftY) : D.IsCover where
  surjective_toB := hB
  etale_liftX := hEtaleX
  surjective_liftX := hSurjX
  etale_liftY := hEtaleY
  surjective_liftY := hSurjY

/-- A diagram is a cover iff `W ⟶ B`, `U ⟶ X ×_B W`, and `V ⟶ Y ×_B W` are étale
surjective. -/
theorem isCover_iff (D : EtaleDiagram X Y) :
    D.IsCover ↔
      Surjective D.toB ∧ Etale D.liftX ∧ Surjective D.liftX ∧ Etale D.liftY ∧
        Surjective D.liftY := by
  constructor
  · intro h
    exact ⟨h.surjective_toB, h.etale_liftX, h.surjective_liftX,
      h.etale_liftY, h.surjective_liftY⟩
  · rintro ⟨hB, hEtaleX, hSurjX, hEtaleY, hSurjY⟩
    exact IsCover.of D hB hEtaleX hSurjX hEtaleY hSurjY

/-- The spaces `U` and `V` are Tor independent over `W`. -/
def torIndependent (D : EtaleDiagram X Y) : Prop :=
  AlgebraicSpace.TorIndependentOver (Over.mk D.fst) (Over.mk D.snd)

/-- `torIndependent` is Tor independence of `Over.mk D.fst` and `Over.mk D.snd`. -/
theorem torIndependent_iff (D : EtaleDiagram X Y) :
    D.torIndependent ↔
      AlgebraicSpace.TorIndependentOver (Over.mk D.fst) (Over.mk D.snd) :=
  Iff.rfl

end EtaleDiagram

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- For every commutative diagram with étale vertical arrows, `U` and `V` are Tor
independent over `W`. -/
def forallEtale (X Y : Over B) : Prop :=
  ∀ D : EtaleDiagram X Y, D.torIndependent

/-- `forallEtale` is the universal étale-vertical Tor-independence condition. -/
theorem forallEtale_iff (X Y : Over B) :
    forallEtale X Y ↔ ∀ D : EtaleDiagram X Y, D.torIndependent :=
  Iff.rfl

namespace forallEtale

/-- Tor independence of `U` and `V` over `W` on a given étale vertical diagram. -/
theorem apply {X Y : Over B} (h : forallEtale X Y) (D : EtaleDiagram X Y) :
    D.torIndependent :=
  h D

end forallEtale

/-- There is a commutative étale-vertical diagram with étale-surjective maps
`W ⟶ B`, `U ⟶ X ×_B W`, and `V ⟶ Y ×_B W` such that `U` and `V` are Tor independent
over `W`. -/
def existsEtaleCover (X Y : Over B) : Prop :=
  ∃ D : EtaleDiagram X Y, D.IsCover ∧ D.torIndependent

/-- `existsEtaleCover` is the existence of an étale-surjective covering diagram on
which `U` and `V` are Tor independent over `W`. -/
theorem existsEtaleCover_iff (X Y : Over B) :
    existsEtaleCover X Y ↔ ∃ D : EtaleDiagram X Y, D.IsCover ∧ D.torIndependent :=
  Iff.rfl

/-- A commutative diagram as in `EtaleDiagram`, with `U`, `V`, and `W` schemes over
`S`. -/
structure SchemeEtaleDiagram (X Y : Over B) where
  /-- The scheme `U` over `S`. -/
  U : Over S
  /-- The scheme `V` over `S`. -/
  V : Over S
  /-- The scheme `W` over `S`. -/
  W : Over S
  /-- The vertical morphism `U ⟶ X` of algebraic spaces. -/
  toX : ofOver U ⟶ X.left
  /-- The vertical morphism `V ⟶ Y` of algebraic spaces. -/
  toY : ofOver V ⟶ Y.left
  /-- The vertical morphism `W ⟶ B` of algebraic spaces. -/
  toB : ofOver W ⟶ B
  /-- The horizontal morphism `U ⟶ W` of schemes over `S`. -/
  fst : U ⟶ W
  /-- The horizontal morphism `V ⟶ W` of schemes over `S`. -/
  snd : V ⟶ W
  /-- The left square commutes after applying `ofOverMap`. -/
  sqX : CommSq toX (ofOverMap fst) X.hom toB
  /-- The right square commutes after applying `ofOverMap`. -/
  sqY : CommSq toY (ofOverMap snd) Y.hom toB
  /-- The morphism `U ⟶ X` is étale. -/
  etale_toX : Etale toX
  /-- The morphism `V ⟶ Y` is étale. -/
  etale_toY : Etale toY
  /-- The morphism `W ⟶ B` is étale. -/
  etale_toB : Etale toB

namespace SchemeEtaleDiagram

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {X Y : Over B}

/-- The algebraic-space diagram obtained by viewing the schemes as algebraic spaces. -/
def toEtaleDiagram (D : SchemeEtaleDiagram X Y) : EtaleDiagram X Y where
  U := ofOver D.U
  V := ofOver D.V
  W := ofOver D.W
  toX := D.toX
  toY := D.toY
  toB := D.toB
  fst := ofOverMap D.fst
  snd := ofOverMap D.snd
  sqX := D.sqX
  sqY := D.sqY
  etale_toX := D.etale_toX
  etale_toY := D.etale_toY
  etale_toB := D.etale_toB

/-- `toEtaleDiagram` views the schemes `U`, `V`, `W` as algebraic spaces via `ofOver`. -/
theorem toEtaleDiagram_spec (D : SchemeEtaleDiagram X Y) :
    D.toEtaleDiagram.U = ofOver D.U ∧ D.toEtaleDiagram.V = ofOver D.V ∧
      D.toEtaleDiagram.W = ofOver D.W :=
  ⟨rfl, rfl, rfl⟩

/-- The schemes `U` and `V` are Tor independent over `W` in the sense of
`Scheme.TorIndependentOver`. -/
def schemeTorIndependent (D : SchemeEtaleDiagram X Y) : Prop :=
  Scheme.TorIndependentOver (Over.mk D.fst.left) (Over.mk D.snd.left)

/-- `schemeTorIndependent` is scheme-level Tor independence of `U` and `V` over `W`. -/
theorem schemeTorIndependent_iff (D : SchemeEtaleDiagram X Y) :
    D.schemeTorIndependent ↔
      Scheme.TorIndependentOver (Over.mk D.fst.left) (Over.mk D.snd.left) :=
  Iff.rfl

end SchemeEtaleDiagram

/-- There is a covering diagram as in `existsEtaleCover` with `U`, `V`, `W` schemes
such that `U` and `V` are Tor independent over `W` as schemes. -/
def existsSchemeCover (X Y : Over B) : Prop :=
  ∃ D : SchemeEtaleDiagram X Y, D.toEtaleDiagram.IsCover ∧ D.schemeTorIndependent

/-- `existsSchemeCover` is the existence of a representable étale-surjective covering
diagram on which `U` and `V` are Tor independent as schemes over `W`. -/
theorem existsSchemeCover_iff (X Y : Over B) :
    existsSchemeCover X Y ↔
      ∃ D : SchemeEtaleDiagram X Y, D.toEtaleDiagram.IsCover ∧ D.schemeTorIndependent :=
  Iff.rfl

/-- Algebraic-space Tor independence agrees with scheme-level Tor independence when
`X`, `Y`, and `B` are schemes over `S`. -/
theorem ofOver_iff {B X Y : Over S} (f : X ⟶ B) (g : Y ⟶ B) :
    AlgebraicSpace.TorIndependentOver (Over.mk (ofOverMap f)) (Over.mk (ofOverMap g)) ↔
      Scheme.TorIndependentOver (Over.mk f.left) (Over.mk g.left) :=
  sorry

/-- Let `S` be a scheme. Let `B` be an algebraic space over `S`. Let
`X`, `Y` be algebraic spaces over `B`. The following are equivalent: `X` and `Y`
are Tor independent over `B`; for every commutative diagram with étale vertical
arrows `U ⟶ X`, `W ⟶ B`, `V ⟶ Y`, the spaces `U` and `V` are Tor independent over
`W`; for some such diagram with `W ⟶ B`, `U ⟶ X ×_B W`, and `V ⟶ Y ×_B W` étale
surjective, the spaces `U` and `V` are Tor independent over `W`; and for some such
covering diagram with `U`, `V`, `W` schemes, the schemes `U` and `V` are Tor
independent over `W` in the sense of `Scheme.TorIndependentOver`. -/
theorem tfae (X Y : Over B) :
    List.TFAE [AlgebraicSpace.TorIndependentOver X Y, forallEtale X Y,
      existsEtaleCover X Y, existsSchemeCover X Y] :=
  sorry

/-- Tor independence over `B` is equivalent to Tor independence of `U` and `V` over
`W` for every étale vertical diagram. -/
theorem iff_forallEtale (X Y : Over B) :
    AlgebraicSpace.TorIndependentOver X Y ↔ forallEtale X Y :=
  sorry

/-- Tor independence over `B` is equivalent to the existence of an étale-surjective
covering diagram on which `U` and `V` are Tor independent over `W`. -/
theorem iff_existsEtaleCover (X Y : Over B) :
    AlgebraicSpace.TorIndependentOver X Y ↔ existsEtaleCover X Y :=
  sorry

/-- Tor independence over `B` is equivalent to the existence of a representable
étale-surjective covering diagram on which `U` and `V` are Tor independent as
schemes over `W`. -/
theorem iff_existsSchemeCover (X Y : Over B) :
    AlgebraicSpace.TorIndependentOver X Y ↔ existsSchemeCover X Y :=
  sorry

end TorIndependentOver

end AlgebraicGeometry.AlgebraicSpace
