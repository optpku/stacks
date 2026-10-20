module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Composition
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change for modules on ringed sites

This file separates three reusable layers: pseudofunctorial direct and inverse images for a
commutative square, the formal mate of an arbitrary inverse-image/direct-image comparison, and
the bridge from pushforward presentations of vertical inverse images to those comparisons.
Geometric criteria for producing a presentation or comparison remain in their site-specific leaf.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ w z

namespace RingedSite.Hom

namespace CommSq

variable {X : RingedSite.{u₀, v₀, w}} {X' : RingedSite.{u₁, v₁, w}}
variable {Y : RingedSite.{u₂, v₂, w}} {Y' : RingedSite.{u₃, v₃, w}}

/-- The pseudofunctorial direct-image isomorphism attached to a commutative square of
ringed-site morphisms. This is the presentation-independent formal core of direct-image base
change when the two vertical inverse images are themselves presented as direct images. -/
@[stacks 0FN4 "(1), pushforward core"]
noncomputable def pushforwardIso
    {i : Hom X X'} {f' : Hom X' Y'} {f : Hom X Y} {j : Hom Y Y'}
    (h : Hom.comp i f' = Hom.comp f j) :
    i.modulePushforward.{z} ⋙ f'.modulePushforward.{z} ≅
      f.modulePushforward.{z} ⋙ j.modulePushforward.{z} :=
  modulePushforwardCompIso.{z} i f' ≪≫
    eqToIso (congrArg (fun k : Hom X Y' ↦ k.modulePushforward.{z}) h) ≪≫
      (modulePushforwardCompIso.{z} f j).symm

section Pullback

variable {i : Hom X X'} {f' : Hom X' Y'} {f : Hom X Y} {j : Hom Y Y'}
variable [(i.modulePushforward.{z}).IsRightAdjoint]
variable [(f'.modulePushforward.{z}).IsRightAdjoint]
variable [(f.modulePushforward.{z}).IsRightAdjoint]
variable [(j.modulePushforward.{z}).IsRightAdjoint]

/-- The inverse-image comparison for a commutative square, obtained canonically as the mate of
`CommSq.pushforwardIso`.  Unlike an implementation through pullback composition, this interface
does not require callers to provide adjointness instances for either composite morphism. -/
@[stacks 0FN4 "(2), pullback core"]
noncomputable def pullbackIso (h : Hom.comp i f' = Hom.comp f j) :
    f'.modulePullback.{z} ⋙ i.modulePullback.{z} ≅
      j.modulePullback.{z} ⋙ f.modulePullback.{z} :=
  ((conjugateIsoEquiv
    ((modulePullbackPushforwardAdjunction.{z} f').comp
      (modulePullbackPushforwardAdjunction.{z} i))
    ((modulePullbackPushforwardAdjunction.{z} j).comp
      (modulePullbackPushforwardAdjunction.{z} f))).symm
        (pushforwardIso h)).symm

end Pullback

-- The displayed isomorphism is assembled entirely from the canonical composition comparisons
-- and equality transport for module pushforwards.

end CommSq

namespace BaseChange

variable {X' : RingedSite.{u₀, v₀, w}} {X : RingedSite.{u₁, v₁, w}}
variable {Y' : RingedSite.{u₂, v₂, w}} {Y : RingedSite.{u₃, v₃, w}}
variable (g' : Hom X' X) (f' : Hom X' Y') (f : Hom X Y) (g : Hom Y' Y)
variable [(g'.modulePushforward.{z}).IsRightAdjoint]
variable [(f'.modulePushforward.{z}).IsRightAdjoint]
variable [(f.modulePushforward.{z}).IsRightAdjoint]
variable [(g.modulePushforward.{z}).IsRightAdjoint]

/-- The module base-change map obtained as the mate of a square of pullback functors.  The
natural transformation is primary; invertibility is a separate Beck--Chevalley property. -/
@[stacks 0FN3 "base-change map", stacks 0FN4 "base-change map"]
noncomputable def comparison
    (square :
      TwoSquare g.modulePullback.{z} f.modulePullback.{z}
        f'.modulePullback.{z} g'.modulePullback.{z}) :
    f.modulePushforward.{z} ⋙ g.modulePullback.{z} ⟶
      g'.modulePullback.{z} ⋙ f'.modulePushforward.{z} :=
  (mateEquiv
    (modulePullbackPushforwardAdjunction.{z} f)
    (modulePullbackPushforwardAdjunction.{z} f') square).natTrans

/-- The module base-change map attached to a strictly commutative square of ringed-site
morphisms. -/
@[stacks 0FN4 "strict square base-change map"]
noncomputable def comparisonOfCommSq
    (h : Hom.comp g' f = Hom.comp f' g) :
    f.modulePushforward.{z} ⋙ g.modulePullback.{z} ⟶
      g'.modulePullback.{z} ⋙ f'.modulePushforward.{z} :=
  comparison g' f' f g
    (CommSq.pullbackIso h).inv

/-- An invertible module base-change map, packaged as its canonical natural isomorphism. -/
noncomputable def comparisonIso
    (square :
      TwoSquare g.modulePullback.{z} f.modulePullback.{z}
        f'.modulePullback.{z} g'.modulePullback.{z})
    [IsIso (comparison g' f' f g square)] :
    f.modulePushforward.{z} ⋙ g.modulePullback.{z} ≅
      g'.modulePullback.{z} ⋙ f'.modulePushforward.{z} :=
  asIso (comparison g' f' f g square)

section LowerShriek

variable [(g'.modulePullback.{z}).IsRightAdjoint]
variable [(g.modulePullback.{z}).IsRightAdjoint]

/-- The lower-shriek mate of a module base-change map. -/
@[stacks 0FN3 "lower-shriek mate", stacks 0FN4 "lower-shriek mate"]
noncomputable def mate
    (α :
      f.modulePushforward.{z} ⋙ g.modulePullback.{z} ⟶
        g'.modulePullback.{z} ⋙ f'.modulePushforward.{z}) :
    f'.modulePullback.{z} ⋙ g'.moduleLowerShriek ⟶
      g.moduleLowerShriek ⋙ f.modulePullback.{z} :=
  (conjugateEquiv
    ((moduleLowerShriek.adjunction g).comp
      (modulePullbackPushforwardAdjunction.{z} f))
    ((modulePullbackPushforwardAdjunction.{z} f').comp
      (moduleLowerShriek.adjunction g'))).symm α

/-- The lower-shriek mate of an invertible module base-change map is invertible. -/
instance mate_isIso
    (α :
      f.modulePushforward.{z} ⋙ g.modulePullback.{z} ⟶
        g'.modulePullback.{z} ⋙ f'.modulePushforward.{z})
    [IsIso α] :
    IsIso (mate g' f' f g α) := sorry

/-- The lower-shriek mate of an explicit module base-change isomorphism. Taking an isomorphism
as input keeps the inverse data independent of any deferred `IsIso` proof. -/
noncomputable def mateIso
    (e :
      f.modulePushforward.{z} ⋙ g.modulePullback.{z} ≅
        g'.modulePullback.{z} ⋙ f'.modulePushforward.{z}) :
    f'.modulePullback.{z} ⋙ g'.moduleLowerShriek ≅
      g.moduleLowerShriek ⋙ f.modulePullback.{z} :=
  (conjugateIsoEquiv
    ((moduleLowerShriek.adjunction g).comp
      (modulePullbackPushforwardAdjunction.{z} f))
    ((modulePullbackPushforwardAdjunction.{z} f').comp
      (moduleLowerShriek.adjunction g'))).symm e

/-- The forward map of `mateIso` is the lower-shriek mate of the forward base-change map. -/
theorem mateIso_hom
    (e :
      f.modulePushforward.{z} ⋙ g.modulePullback.{z} ≅
        g'.modulePullback.{z} ⋙ f'.modulePushforward.{z}) :
    (mateIso g' f' f g e).hom = mate g' f' f g e.hom := sorry

end LowerShriek

end BaseChange

/-- A presentation of a module pullback as a direct image along a reverse ringed-site morphism. -/
@[stacks 0FN4 "vertical pullback presentation"]
structure PullbackPresentation
    {X' : RingedSite.{u₀, v₀, w}} {X : RingedSite.{u₁, v₁, w}}
    (g : Hom X' X) [(g.modulePushforward.{z}).IsRightAdjoint] where
  /-- The reverse morphism whose direct image presents `g`'s module pullback. -/
  pushforwardHom : Hom X X'
  /-- The chosen identification of module pullback with the presenting direct image. -/
  iso : g.modulePullback.{z} ≅ pushforwardHom.modulePushforward.{z}

namespace PullbackPresentation

variable {X' : RingedSite.{u₀, v₀, w}} {X : RingedSite.{u₁, v₁, w}}
variable {Y' : RingedSite.{u₂, v₂, w}} {Y : RingedSite.{u₃, v₃, w}}
variable {g' : Hom X' X} {f' : Hom X' Y'} {f : Hom X Y} {g : Hom Y' Y}
variable [(g'.modulePushforward.{z}).IsRightAdjoint]
variable [(g.modulePushforward.{z}).IsRightAdjoint]

/-- The module base-change isomorphism obtained from pullback presentations and an arbitrary
isomorphism between the two reverse direct-image composites. -/
@[stacks 0FN4 "pushforward-isomorphism core"]
noncomputable def isoOfPushforwardIso
    (pg' : PullbackPresentation g') (pg : PullbackPresentation g)
    (e : pg'.pushforwardHom.modulePushforward.{z} ⋙ f'.modulePushforward.{z} ≅
      f.modulePushforward.{z} ⋙ pg.pushforwardHom.modulePushforward.{z}) :
    f.modulePushforward.{z} ⋙ g.modulePullback.{z} ≅
      g'.modulePullback.{z} ⋙ f'.modulePushforward.{z} :=
  (Functor.isoWhiskerRight pg'.iso f'.modulePushforward.{z} ≪≫
    e ≪≫
      Functor.isoWhiskerLeft f.modulePushforward.{z} pg.iso.symm).symm

/-- The base-change isomorphism supplied by compatible direct-image presentations of the two
vertical module pullbacks and a strictly commutative reverse square. -/
@[stacks 0FN4 "(1), pullback presentation"]
noncomputable def baseChangeIso
    (pg' : PullbackPresentation g') (pg : PullbackPresentation g)
    (h : Hom.comp pg'.pushforwardHom f' = Hom.comp f pg.pushforwardHom) :
    f.modulePushforward.{z} ⋙ g.modulePullback.{z} ≅
      g'.modulePullback.{z} ⋙ f'.modulePushforward.{z} :=
  isoOfPushforwardIso pg' pg (CommSq.pushforwardIso h)

/-- The canonical map underlying base change from compatible pullback presentations. -/
@[stacks 0FN4 "(1), comparison"]
noncomputable def comparison
    (pg' : PullbackPresentation g') (pg : PullbackPresentation g)
    (h : Hom.comp pg'.pushforwardHom f' = Hom.comp f pg.pushforwardHom) :
    f.modulePushforward.{z} ⋙ g.modulePullback.{z} ⟶
      g'.modulePullback.{z} ⋙ f'.modulePushforward.{z} :=
  (baseChangeIso pg' pg h).hom

/-- The comparison arising from compatible pullback presentations is invertible. -/
theorem comparison_isIso
    (pg' : PullbackPresentation g') (pg : PullbackPresentation g)
    (h : Hom.comp pg'.pushforwardHom f' = Hom.comp f pg.pushforwardHom) :
    IsIso (comparison pg' pg h) := sorry

/-- Compatible pullback presentations give the lower-shriek base-change isomorphism. -/
@[stacks 0FN4 "(2), pullback presentation"]
noncomputable def lowerShriekIso
    [(f'.modulePushforward.{z}).IsRightAdjoint]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g'.modulePullback.{z}).IsRightAdjoint]
    [(g.modulePullback.{z}).IsRightAdjoint]
    (pg' : PullbackPresentation g') (pg : PullbackPresentation g)
    (h : Hom.comp pg'.pushforwardHom f' = Hom.comp f pg.pushforwardHom) :
    f'.modulePullback.{z} ⋙ g'.moduleLowerShriek ≅
      g.moduleLowerShriek ⋙ f.modulePullback.{z} :=
  BaseChange.mateIso g' f' f g
    (baseChangeIso pg' pg h)

end PullbackPresentation

end RingedSite.Hom
