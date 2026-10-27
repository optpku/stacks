/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Specialization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.LocalGeneration
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Relative.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Impurity.Henselization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FiniteType

/-!
# Purity of modules along a fibre of a morphism of algebraic spaces

A finite type quasi-coherent module on a finite type decent morphism of algebraic
spaces is pure above a point of the base when it admits no scheme-valued impurity
that is quasi-finite at the special point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A finite type quasi-coherent module on a finite type decent morphism of
algebraic spaces is pure above a point of the base when it admits no
scheme-valued impurity that is quasi-finite at the special point. -/
def IsPureAlong {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules)
    (f : X ⟶ Y) [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType]
    (y : |Y|) : Prop :=
  ∀ (T : Over S) (h : ofOver T ⟶ Y) (t' t : T.left)
      (ξ : Points (Limits.pullback f h)),
    ¬ (Specializes t' t ∧
        Points.map h (ofOver.pointsEquiv T t) = y ∧
        Points.map (Limits.pullback.snd f h) ξ = ofOver.pointsEquiv T t' ∧
        FiniteType.QuasiFiniteAt h (ofOver.pointsEquiv T t) ∧
        ξ ∈ relativeAssassin (Limits.pullback.snd f h)
          ((pullback (Limits.pullback.fst f h)).obj F) ∧
        ofOver.pointsEquiv T t ∉
          Points.map (Limits.pullback.snd f h) '' closure {ξ})

/-- Purity above a point of the base is the absence of scheme-valued impurities
that are quasi-finite at the special point. -/
theorem isPureAlong_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : |Y|) :
    IsPureAlong F f y ↔
      ∀ (T : Over S) (h : ofOver T ⟶ Y) (t' t : T.left)
          (ξ : Points (Limits.pullback f h)),
        ¬ (Specializes t' t ∧
            Points.map h (ofOver.pointsEquiv T t) = y ∧
            Points.map (Limits.pullback.snd f h) ξ = ofOver.pointsEquiv T t' ∧
            FiniteType.QuasiFiniteAt h (ofOver.pointsEquiv T t) ∧
            ξ ∈ relativeAssassin (Limits.pullback.snd f h)
              ((pullback (Limits.pullback.fst f h)).obj F) ∧
            ofOver.pointsEquiv T t ∉
              Points.map (Limits.pullback.snd f h) '' closure {ξ}) :=
  sorry

namespace IsPureAlong

/-- Purity of a finite-type quasi-coherent module above a point is preserved
by a pointed base change that is quasi-finite at the source point. -/
theorem pullback_of_quasiFiniteAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] [Decent f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (y : |Y|) {Y' : AlgebraicSpace S}
    (g : Y' ⟶ Y) (y' : |Y'|) (hpoint : Points.map g y' = y)
    (hquasi : FiniteType.QuasiFiniteAt g y') (hpure : IsPureAlong F f y) :
    IsPureAlong ((pullback (Limits.pullback.fst f g)).obj F)
      (Limits.pullback.snd f g) y' :=
  sorry


end IsPureAlong

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Purity above `y` is equivalent to the non-existence of an étale-neighbourhood impurity. -/
theorem isPureAlong_iff_not_exists_etaleNeighbourhood (F : X.Modules) (f : X ⟶ Y)
    [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) :
    F.IsPureAlong f y ↔ ¬ Impurity.exists_etaleNeighbourhood F f y :=
  sorry

/-- Purity above `y` is equivalent to the non-existence of an impurity that is quasi-finite
at the special point. -/
theorem isPureAlong_iff_not_exists_quasiFiniteAt (F : X.Modules) (f : X ⟶ Y)
    [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) :
    F.IsPureAlong f y ↔ ¬ Impurity.exists_quasiFiniteAt F f y :=
  sorry

/-- Purity above `y` is equivalent to the non-existence of an impurity over a strict
henselization at a geometric point lying over `y`. -/
theorem isPureAlong_iff_not_exists_strictHenselization (F : X.Modules) (f : X ⟶ Y)
    [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y)
    (ybar : GeometricPoint Y) (hy : ybar.liesOver y) :
    F.IsPureAlong f y ↔ ¬ Impurity.exists_strictHenselization F f y ybar :=
  sorry

/-- A finite type quasi-coherent module is universally pure above `y` when it has no
scheme-valued impurity above `y`. -/
def IsUniversallyPureAlong (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) : Prop :=
  ∀ {T : Over S} (g : ofOver T ⟶ Y) (t' t : T.left)
    (ξ : Points (Limits.pullback f g)),
    Specializes t' t →
      Points.map g (ofOver.pointsEquiv T t) = y →
        ξ ∈ relativeAssassin (Limits.pullback.snd f g)
            ((pullback (Limits.pullback.fst f g)).obj F) →
          Points.map (Limits.pullback.snd f g) ξ = ofOver.pointsEquiv T t' →
            ∃ θ : Points (Limits.pullback f g),
              Specializes ξ θ ∧
                Points.map (Limits.pullback.snd f g) θ = ofOver.pointsEquiv T t

/-- Universal purity above `y` is the absence of every scheme-valued impurity of `F`
above `y`. -/
theorem isUniversallyPureAlong_iff (F : X.Modules) (f : X ⟶ Y)
    [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) :
    F.IsUniversallyPureAlong f y ↔
      ∀ {T : Over S} (g : ofOver T ⟶ Y) (t' t : T.left)
        (ξ : Points (Limits.pullback f g)),
        Specializes t' t →
          Points.map g (ofOver.pointsEquiv T t) = y →
            ξ ∈ relativeAssassin (Limits.pullback.snd f g)
                ((pullback (Limits.pullback.fst f g)).obj F) →
              Points.map (Limits.pullback.snd f g) ξ = ofOver.pointsEquiv T t' →
                ∃ θ : Points (Limits.pullback f g),
                  Specializes ξ θ ∧
                    Points.map (Limits.pullback.snd f g) θ =
                      ofOver.pointsEquiv T t :=
  sorry

/-- A finite type quasi-coherent module is pure relative to `Y` when it is pure above
every point of `Y`. -/
def IsPureOver (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] : Prop :=
  ∀ y : Points Y, F.IsPureAlong f y

/-- Relative purity is purity above every point of the base. -/
theorem isPureOver_iff (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] :
    F.IsPureOver f ↔ ∀ y : Points Y, F.IsPureAlong f y :=
  sorry

/-- A finite type quasi-coherent module is universally pure relative to `Y` when it is
universally pure above every point of `Y`. -/
def IsUniversallyPureOver (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] : Prop :=
  ∀ y : Points Y, F.IsUniversallyPureAlong f y

/-- Universal relative purity is universal purity above every point of the base. -/
theorem isUniversallyPureOver_iff (F : X.Modules) (f : X ⟶ Y)
    [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType] :
    F.IsUniversallyPureOver f ↔ ∀ y : Points Y, F.IsUniversallyPureAlong f y :=
  sorry

namespace IsUniversallyPureAlong

/-- A finite type quasi-coherent module on a finite type decent morphism of algebraic
spaces is universally pure above a point if and only if its pullback along every
pointed base change is pure above the selected point. -/
theorem iff_forall_pointedBaseChange {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) :
    F.IsUniversallyPureAlong f y ↔
      ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y) (y' : Points Y'),
        Points.map g y' = y →
          ((Modules.pullback (Limits.pullback.fst f g)).obj F).IsPureAlong
            (Limits.pullback.snd f g) y' :=
  sorry

end IsUniversallyPureAlong

namespace IsUniversallyPureOver

/-- A finite type quasi-coherent module on a finite type decent morphism of algebraic
spaces is universally pure relative to its base if and only if every base change
is pure relative to the new base. -/
theorem iff_forall_baseChange {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] :
    F.IsUniversallyPureOver f ↔
      ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y),
        ((Modules.pullback (Limits.pullback.fst f g)).obj F).IsPureOver
          (Limits.pullback.snd f g) :=
  sorry

end IsUniversallyPureOver
end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- An algebraic space is pure above `y` when its structure sheaf is pure above `y`. -/
def IsPureAlong (f : X ⟶ Y) [FiniteType f] [Decent f] (y : Points Y) : Prop :=
  Modules.IsPureAlong (SheafOfModules.unit (structureSheaf X) : X.Modules) f y

/-- Purity of an algebraic space above `y` is module purity of its structure sheaf. -/
theorem isPureAlong_iff_structureSheaf (f : X ⟶ Y) [FiniteType f] [Decent f]
    (y : Points Y) :
    IsPureAlong f y ↔
      Modules.IsPureAlong (SheafOfModules.unit (structureSheaf X) : X.Modules) f y :=
  sorry

/-- An algebraic space is pure relative to `Y` when its structure sheaf is pure relative
to `Y`. -/
def IsPureOver (f : X ⟶ Y) [FiniteType f] [Decent f] : Prop :=
  Modules.IsPureOver (SheafOfModules.unit (structureSheaf X) : X.Modules) f

/-- Relative purity of an algebraic space is relative module purity of its structure sheaf. -/
theorem isPureOver_iff_structureSheaf (f : X ⟶ Y) [FiniteType f] [Decent f] :
    IsPureOver f ↔
      Modules.IsPureOver (SheafOfModules.unit (structureSheaf X) : X.Modules) f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
