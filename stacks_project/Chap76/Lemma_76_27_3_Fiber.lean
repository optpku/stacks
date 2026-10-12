/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import stacks_project.Chap67.Lemma_67_15_2_Fiber
public import stacks_project.Chap67.Lemma_67_30_8
public import stacks_project.Chap71.Lemma_71_4_1_Fiber
public import stacks_project.Chap76.Lemma_76_27_3_Gorenstein

/-!
# Closed fibres of étale local ring maps and residue-field fibres

The closed fibre of a morphism of algebraic spaces at a geometric point is the
quotient of `𝒪_{X, x̄}` by the extended maximal ideal of `𝒪_{Y, ȳ}`. Residue-field
fibres of a morphism to a scheme are Gorenstein algebraic spaces when each
residue-field fibre is Gorenstein.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint IsLocalRing MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The closed fibre `𝒪_{X, x̄} ⧸ 𝔪_ȳ 𝒪_{X, x̄}` of a morphism of algebraic spaces
at a geometric point `xbar`, where `ȳ = xbar.map f`. -/
noncomputable def etaleLocalRingClosedFiber {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (xbar : GeometricPoint X) : Type u :=
  etaleLocalRing X xbar ⧸
    (maximalIdeal (etaleLocalRing Y (xbar.map f))).map (etaleLocalRingMap f xbar)

/-- The closed fibre is the quotient of the source étale local ring by the
extension of the maximal ideal of the target étale local ring. -/
theorem etaleLocalRingClosedFiber_def {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (xbar : GeometricPoint X) :
    etaleLocalRingClosedFiber f xbar =
      (etaleLocalRing X xbar ⧸
        (maximalIdeal (etaleLocalRing Y (xbar.map f))).map
          (etaleLocalRingMap f xbar)) :=
  sorry

/-- The closed fibre of an étale local ring map is a commutative ring. -/
noncomputable instance etaleLocalRingClosedFiber.instCommRing
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) : CommRing (etaleLocalRingClosedFiber f xbar) :=
  inferInstanceAs
    (CommRing
      (etaleLocalRing X xbar ⧸
        (maximalIdeal (etaleLocalRing Y (xbar.map f))).map
          (etaleLocalRingMap f xbar)))

/-- The closed fibre of an étale local ring map is a local ring. -/
instance etaleLocalRingClosedFiber.instIsLocalRing {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (xbar : GeometricPoint X) :
    IsLocalRing (etaleLocalRingClosedFiber f xbar) :=
  sorry

/-- The étale local ring map of a morphism of algebraic spaces is a local
homomorphism. -/
instance etaleLocalRingMap.instIsLocalHom {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (xbar : GeometricPoint X) :
    IsLocalHom (etaleLocalRingMap f xbar) :=
  sorry

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
  sorry

/-- The fibres of the base change `X_V ⟶ V` along a morphism from a scheme are
Gorenstein algebraic spaces. -/
def fibersGorenstein {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : ofOver V ⟶ Y) : Prop :=
  ∀ v : V.left,
    IsGorenstein (residueFiberOver (pullbackAlongScheme.snd f b) (𝟙 (ofOver V)) v)

/-- `fibersGorenstein f b` unpacks as Gorensteinness of every residue-field fibre
of `pullbackAlongScheme.snd f b`. -/
theorem fibersGorenstein_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {V : Over S} (b : ofOver V ⟶ Y) :
    fibersGorenstein f b ↔
      ∀ v : V.left,
        IsGorenstein
          (residueFiberOver (pullbackAlongScheme.snd f b) (𝟙 (ofOver V)) v) :=
  sorry

namespace fibersGorenstein

/-- If the fibres of `X_V ⟶ V` are Gorenstein, then the residue-field fibre at
`v` is a Gorenstein algebraic space. -/
theorem apply {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {V : Over S}
    {b : ofOver V ⟶ Y} (h : fibersGorenstein f b) (v : V.left) :
    IsGorenstein (residueFiberOver (pullbackAlongScheme.snd f b) (𝟙 (ofOver V)) v) :=
  sorry

end fibersGorenstein

namespace Gorenstein

/-- There is a surjective étale morphism from a scheme to `Y` along which the
residue-field fibres of the base change of `f` are Gorenstein algebraic
spaces. -/
def existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (V : Over S) (b : ofOver V ⟶ Y),
    (over (@AlgebraicGeometry.Etale)).presheaf b ∧
      Surjective b ∧ fibersGorenstein f b

/-- `existsSurjectiveEtaleTarget f` unpacks as a surjective étale scheme chart of
`Y` whose pullback has Gorenstein residue-field fibres. -/
theorem existsSurjectiveEtaleTarget_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    existsSurjectiveEtaleTarget f ↔
      ∃ (V : Over S) (b : ofOver V ⟶ Y),
        (over (@AlgebraicGeometry.Etale)).presheaf b ∧
          Surjective b ∧ fibersGorenstein f b :=
  sorry

namespace existsSurjectiveEtaleTarget

/-- A surjective étale scheme chart of `Y` whose pullback has Gorenstein
residue-field fibres witnesses `existsSurjectiveEtaleTarget f`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {V : Over S}
    (b : ofOver V ⟶ Y) (hb_etale : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (hb_surj : Surjective b)
    (hfib : fibersGorenstein f b) :
    existsSurjectiveEtaleTarget f :=
  sorry

/-- `existsSurjectiveEtaleTarget f` supplies a surjective étale scheme chart of
`Y` whose pullback has Gorenstein residue-field fibres. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : existsSurjectiveEtaleTarget f) :
    ∃ (V : Over S) (b : ofOver V ⟶ Y),
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        Surjective b ∧ fibersGorenstein f b :=
  sorry

end existsSurjectiveEtaleTarget

/-- For every étale morphism from a scheme to `Y`, the residue-field fibres of
the base change of `f` are Gorenstein algebraic spaces. -/
def forallEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ (V : Over S) (b : ofOver V ⟶ Y),
    (over (@AlgebraicGeometry.Etale)).presheaf b →
      fibersGorenstein f b

/-- `forallEtaleTarget f` unpacks as Gorenstein residue-field fibres after every
étale scheme base change of `f`. -/
theorem forallEtaleTarget_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    forallEtaleTarget f ↔
      ∀ (V : Over S) (b : ofOver V ⟶ Y),
        (over (@AlgebraicGeometry.Etale)).presheaf b →
          fibersGorenstein f b :=
  sorry

namespace forallEtaleTarget

/-- The universal étale-scheme-base-change condition witnesses
`forallEtaleTarget f`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ (V : Over S) (b : ofOver V ⟶ Y),
      (over (@AlgebraicGeometry.Etale)).presheaf b →
        fibersGorenstein f b) :
    forallEtaleTarget f :=
  sorry

/-- If `forallEtaleTarget f`, then every étale scheme base change of `f` has
Gorenstein residue-field fibres. -/
theorem apply {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : forallEtaleTarget f) {V : Over S} (b : ofOver V ⟶ Y)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b) :
    fibersGorenstein f b :=
  sorry

end forallEtaleTarget

end Gorenstein

end AlgebraicGeometry.AlgebraicSpace
