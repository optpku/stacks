/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Relative.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedPoints.Impurity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Impurity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictHenselization.Neighborhood

/-!
# Equivalent characterizations of impurities above a point

For a finite type decent morphism and a finite type quasi-coherent module,
impurity existence can be tested over a strict henselization, by specialization
of relative associated points, over an étale neighbourhood, or over a morphism
quasi-finite at the special point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace Impurity

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- There exists an impurity of `F` above `y` whose base-change morphism is
`strictHenselizationHomOf N` for some small étale neighbourhood of `ybar`, with
special point `closedPoint N`. -/
def exists_strictHenselization (F : X.Modules) (f : X ⟶ Y) (y : Points Y)
    (ybar : GeometricPoint Y) : Prop :=
  ∃ (N : SmallEtaleNeighborhood ybar)
    (y' : (SchemeOver.mk (strictHenselizationHomOf N)).left.left)
    (ξ : Points (Limits.pullback f (strictHenselizationHomOf N))),
    IsImpurity f F y (SchemeOver.mk (strictHenselizationHomOf N)) y'
      (closedPoint N) ξ

/-- Existence over a strict henselization means that a neighbourhood presentation
admits a generic endpoint and an impurity point with the prescribed closed endpoint. -/
theorem exists_strictHenselization_iff (F : X.Modules) (f : X ⟶ Y) (y : Points Y)
    (ybar : GeometricPoint Y) :
    exists_strictHenselization F f y ybar ↔
      ∃ (N : SmallEtaleNeighborhood ybar)
        (y' : (SchemeOver.mk (strictHenselizationHomOf N)).left.left)
        (ξ : Points (Limits.pullback f (strictHenselizationHomOf N))),
        IsImpurity f F y (SchemeOver.mk (strictHenselizationHomOf N)) y'
          (closedPoint N) ξ := by
  rfl

/-- There exists a relative associated point of the pullback of `F` to `X^{sh}`
that does not specialize into the closed fibre over `closedPoint N`. -/
def exists_relativeAssassin_not_specializes_closedFiber (F : X.Modules)
    (f : X ⟶ Y) (y : Points Y) (ybar : GeometricPoint Y) : Prop :=
  ∃ (N : SmallEtaleNeighborhood ybar)
    (ξ : Points (Limits.pullback f (strictHenselizationHomOf N))),
    ξ ∈ relativeAssassin (Limits.pullback.snd f (strictHenselizationHomOf N))
        ((Modules.pullback (Limits.pullback.fst f (strictHenselizationHomOf N))).obj F) ∧
      ¬ ∃ θ : Points (Limits.pullback f (strictHenselizationHomOf N)),
          Specializes ξ θ ∧ θ ∈ closedFiber f N

/-- The associated-point criterion is the existence, in a neighbourhood
presentation, of a relative associated point with no specialization into the closed fibre. -/
theorem exists_relativeAssassin_not_specializes_closedFiber_iff (F : X.Modules)
    (f : X ⟶ Y) (y : Points Y) (ybar : GeometricPoint Y) :
    exists_relativeAssassin_not_specializes_closedFiber F f y ybar ↔
      ∃ (N : SmallEtaleNeighborhood ybar)
        (ξ : Points (Limits.pullback f (strictHenselizationHomOf N))),
        ξ ∈ relativeAssassin (Limits.pullback.snd f (strictHenselizationHomOf N))
            ((Modules.pullback (Limits.pullback.fst f (strictHenselizationHomOf N))).obj F) ∧
          ¬ ∃ θ : Points (Limits.pullback f (strictHenselizationHomOf N)),
              Specializes ξ θ ∧ θ ∈ closedFiber f N := by
  rfl

/-- There exists an impurity of `F` above `y` whose base-change morphism is étale. -/
def exists_etaleNeighbourhood (F : X.Modules) (f : X ⟶ Y) (y : Points Y) : Prop :=
  ∃ I : Impurity F f y, AlgebraicSpace.Etale I.g

/-- An étale-neighbourhood impurity exists exactly when an impurity has an étale
base-change morphism. -/
theorem exists_etaleNeighbourhood_iff (F : X.Modules) (f : X ⟶ Y) (y : Points Y) :
    exists_etaleNeighbourhood F f y ↔
      ∃ I : Impurity F f y, AlgebraicSpace.Etale I.g := by
  rfl

/-- There exists an impurity of `F` above `y` that is quasi-finite at the special
point. -/
def exists_quasiFiniteAt (F : X.Modules) (f : X ⟶ Y) (y : Points Y) : Prop :=
  ∃ I : Impurity F f y,
    FiniteType.QuasiFiniteAt I.g (ofOver.pointsEquiv I.T I.specialPoint)

/-- A quasi-finite impurity exists exactly when an impurity's base-change morphism
is quasi-finite at its special endpoint. -/
theorem exists_quasiFiniteAt_iff (F : X.Modules) (f : X ⟶ Y) (y : Points Y) :
    exists_quasiFiniteAt F f y ↔
      ∃ I : Impurity F f y,
        FiniteType.QuasiFiniteAt I.g (ofOver.pointsEquiv I.T I.specialPoint) := by
  rfl

/-- For a finite type decent morphism and a finite type quasi-coherent module,
the existence of an impurity above a point is equivalent to its existence over
a strict henselization, to a relative associated point that does not specialize
into the closed fibre, to existence over an étale neighbourhood, and to
existence over a morphism quasi-finite at the special point. -/
theorem existence_tfae (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) (ybar : GeometricPoint Y)
    (hy : ybar.liesOver y) :
    List.TFAE
      [exists_strictHenselization F f y ybar,
        exists_relativeAssassin_not_specializes_closedFiber F f y ybar,
        exists_etaleNeighbourhood F f y, exists_quasiFiniteAt F f y] :=
  sorry

/-- For a finite type decent morphism and a finite type quasi-coherent module,
an impurity over a strict henselization at `ybar` exists if and only if some relative associated point of `F^{sh}` fails to specialize
into the closed fibre. -/
theorem strictHenselization_iff_associatedPoint
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) (ybar : GeometricPoint Y)
    (hy : ybar.liesOver y) :
    exists_strictHenselization F f y ybar ↔
      exists_relativeAssassin_not_specializes_closedFiber F f y ybar :=
  sorry

/-- For a finite type decent morphism and a finite type quasi-coherent module,
an impurity over a strict henselization at `ybar` exists if and only if an étale-neighbourhood impurity above `y` exists. -/
theorem exists_strictHenselization_iff_exists_etaleNeighbourhood (F : X.Modules)
    (f : X ⟶ Y) [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType]
    (y : Points Y) (ybar : GeometricPoint Y) (hy : ybar.liesOver y) :
    exists_strictHenselization F f y ybar ↔ exists_etaleNeighbourhood F f y :=
  sorry

/-- For a finite type decent morphism and a finite type quasi-coherent module,
an étale-neighbourhood impurity above `y` exists if and only if an impurity quasi-finite at its special point exists. -/
theorem exists_etaleNeighbourhood_iff_exists_quasiFiniteAt (F : X.Modules)
    (f : X ⟶ Y) [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType]
    (y : Points Y) :
    exists_etaleNeighbourhood F f y ↔ exists_quasiFiniteAt F f y :=
  sorry

end Impurity
end AlgebraicGeometry.AlgebraicSpace.Modules
