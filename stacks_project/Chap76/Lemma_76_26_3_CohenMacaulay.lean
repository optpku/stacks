module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
public import stacks_project.Chap66.Definition_66_7_2
public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap66.Lemma_66_29_5_Comparison
public import stacks_project.Chap66.Remark_66_7_3_EtaleLocal
public import stacks_project.Chap67.Lemma_67_15_2_Fiber
public import stacks_project.Chap67.Lemma_67_22_5
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap71.Lemma_71_4_1_Fiber
public import stacks_project.Chap71.Lemma_71_4_6_Fiber
public import stacks_project.Chap76.Lemma_76_26_1_FiberStalkCohenMacaulay

/-!
# Cohen–Macaulay morphisms of algebraic spaces

A morphism of algebraic spaces is Cohen–Macaulay at a point when it is flat
there and some étale scheme square has Cohen–Macaulay fibre stalk, in the
sense of Stacks Definition 76.26.2, using the germ property
`fiberStalkCohenMacaulay` of Lemma 76.26.1. The global property is the
corresponding pointwise class. The fibre ring at a geometric point is the
quotient of the source étale local ring by the maximal ideal of the target
étale local ring.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry MorphismProperty
open Scheme.Germ.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The fibre ring `𝒪_{X, xbar} ⧸ m_{ȳ} 𝒪_{X, xbar}` of a morphism of algebraic
spaces at a geometric point `xbar`, where `ȳ = xbar.map f`. -/
def fiberEtaleLocalRing {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) : Type u :=
  etaleLocalRing X xbar ⧸
    Ideal.map (etaleLocalRingMap f xbar)
      (IsLocalRing.maximalIdeal (etaleLocalRing Y (xbar.map f)))

/-- `fiberEtaleLocalRing f xbar` is the quotient of `etaleLocalRing X xbar` by
the extension of the maximal ideal of `etaleLocalRing Y (xbar.map f)`. -/
theorem fiberEtaleLocalRing_def {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (xbar : GeometricPoint X) :
    fiberEtaleLocalRing f xbar =
      (etaleLocalRing X xbar ⧸
        Ideal.map (etaleLocalRingMap f xbar)
          (IsLocalRing.maximalIdeal (etaleLocalRing Y (xbar.map f)))) :=
  sorry

/-- The fibre ring at a geometric point is a commutative ring, as a quotient of
the source étale local ring. -/
instance fiberEtaleLocalRing.instCommRing {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (xbar : GeometricPoint X) :
    CommRing (fiberEtaleLocalRing f xbar) :=
  inferInstanceAs
    (CommRing
      (etaleLocalRing X xbar ⧸
        Ideal.map (etaleLocalRingMap f xbar)
          (IsLocalRing.maximalIdeal (etaleLocalRing Y (xbar.map f)))))

/-- A morphism `f : X ⟶ Y` of algebraic spaces is Cohen–Macaulay at a point `x`
of `X` if it is flat at `x` and some étale scheme square through `x` has
Cohen–Macaulay fibre stalk. -/
def CohenMacaulayAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  FlatAt f x ∧ existsEtaleSquareAt fiberStalkCohenMacaulay f x

/-- Cohen–Macaulayness at a point unpacks as flatness at that point together
with an étale scheme square whose induced germ morphism has Cohen–Macaulay
fibre stalk. -/
theorem cohenMacaulayAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    CohenMacaulayAt f x ↔
      FlatAt f x ∧ existsEtaleSquareAt fiberStalkCohenMacaulay f x :=
  sorry

/-- Pointwise Cohen–Macaulayness is equivalent to flatness at the point together
with the fibre-stalk Cohen–Macaulay property on every étale scheme square
through that point. -/
theorem cohenMacaulayAt_iff_forallEtaleSquareAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    CohenMacaulayAt f x ↔
      FlatAt f x ∧ forallEtaleSquareAt fiberStalkCohenMacaulay f x :=
  sorry

/-- The germ morphism induced by a morphism of schemes over `S` has Cohen–Macaulay
fibre stalk if and only if the fibre stalk of the underlying scheme morphism at
the distinguished source point is a Cohen–Macaulay ring. -/
theorem fiberStalkCohenMacaulay_ofOverGermHom_iff {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (u : U.left) :
    fiberStalkCohenMacaulay (ofOverGermHom h u) ↔
      CohenMacaulayRing (h.left.fiberStalkAt u) :=
  sorry

namespace CohenMacaulayAt

/-- A morphism that is Cohen–Macaulay at a point is flat there. -/
theorem flatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} (h : CohenMacaulayAt f x) : FlatAt f x :=
  sorry

/-- Flatness at `x` together with an étale scheme square through `x` whose
induced germ morphism has Cohen–Macaulay fibre stalk witnesses
`CohenMacaulayAt f x`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {x : Points X}
    (hflat : FlatAt f x)
    (hQ : existsEtaleSquareAt fiberStalkCohenMacaulay f x) :
    CohenMacaulayAt f x :=
  sorry

end CohenMacaulayAt

/-- A morphism `f : X ⟶ Y` of algebraic spaces is Cohen–Macaulay if it is
Cohen–Macaulay at every point of `X`. -/
class CohenMacaulay {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop where
  /-- The morphism is Cohen–Macaulay at every point of the source. -/
  pointwise : ∀ x : Points X, CohenMacaulayAt f x

/-- A morphism of algebraic spaces is Cohen–Macaulay if and only if it is
Cohen–Macaulay at every point of its source. -/
theorem cohenMacaulay_iff_forall_cohenMacaulayAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    CohenMacaulay f ↔ ∀ x : Points X, CohenMacaulayAt f x :=
  sorry

namespace CohenMacaulay

/-- A Cohen–Macaulay morphism of algebraic spaces is Cohen–Macaulay at every
point of its source, and in particular flat. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [CohenMacaulay f] :
    (∀ x : Points X, CohenMacaulayAt f x) ∧ Flat f :=
  sorry

/-- Every Cohen–Macaulay morphism of algebraic spaces is flat. -/
instance instFlat {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [CohenMacaulay f] : Flat f :=
  sorry

/-- The identity morphism of an algebraic space is Cohen–Macaulay. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : CohenMacaulay (𝟙 X) :=
  sorry

/-- A Cohen–Macaulay morphism of schemes over `S` is Cohen–Macaulay as a
morphism of algebraic spaces. -/
instance ofOverMap {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.CohenMacaulay h.left] : CohenMacaulay (ofOverMap h) :=
  sorry

end CohenMacaulay

/-- The fibres of the base change `X_V ⟶ V` along a morphism from a scheme are
Cohen–Macaulay algebraic spaces. -/
def fibersCohenMacaulay {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : ofOver V ⟶ Y) : Prop :=
  ∀ v : V.left,
    hasEtaleLocal (Scheme.CohenMacaulay : ObjectProperty Scheme.{u})
      (residueFiberOver (pullbackAlongScheme.snd f b) (𝟙 (ofOver V)) v)

/-- `fibersCohenMacaulay f b` unpacks as Cohen–Macaulayness of every
residue-field fibre of `pullbackAlongScheme.snd f b`. -/
theorem fibersCohenMacaulay_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {V : Over S} (b : ofOver V ⟶ Y) :
    fibersCohenMacaulay f b ↔
      ∀ v : V.left,
        hasEtaleLocal (Scheme.CohenMacaulay : ObjectProperty Scheme.{u})
          (residueFiberOver (pullbackAlongScheme.snd f b) (𝟙 (ofOver V)) v) :=
  sorry

namespace fibersCohenMacaulay

/-- If the fibres of `X_V ⟶ V` are Cohen–Macaulay, then the residue-field fibre
at `v` is a Cohen–Macaulay algebraic space. -/
theorem apply {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {V : Over S}
    {b : ofOver V ⟶ Y} (h : fibersCohenMacaulay f b) (v : V.left) :
    hasEtaleLocal (Scheme.CohenMacaulay : ObjectProperty Scheme.{u})
      (residueFiberOver (pullbackAlongScheme.snd f b) (𝟙 (ofOver V)) v) :=
  sorry

end fibersCohenMacaulay

end AlgebraicGeometry.AlgebraicSpace
