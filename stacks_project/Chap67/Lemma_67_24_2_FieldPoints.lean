module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.FieldPoints

/-!
# Field-valued point comparison API

Typed checks expose the canonical point-comparison API. The structural-map
compatibility names refer to the canonical scheme-realization morphism.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structural morphism of an algebraic space to its base scheme. -/
abbrev toBase {S : Scheme.{u}} (X : AlgebraicSpace S) : X ⟶ ofOver (Over.mk (𝟙 S)) :=
  SchemeRealization.toBase X

/-- Every morphism to the base scheme equals the structural morphism. -/
theorem eq_toBase {S : Scheme.{u}} {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) : f = toBase X :=
  SchemeRealization.eq_toBase f

#check (AlgebraicGeometry.AlgebraicSpace.toBase_app :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (T : (Over S)ᵒᵖ)
    (x : X.functorOfPoints.obj T),
    (SchemeRealization.toBase X).app T x = Over.homMk T.unop.hom)

namespace Points

#check (AlgebraicGeometry.AlgebraicSpace.Points.base :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X),
    S)

#check (AlgebraicGeometry.AlgebraicSpace.Points.base_mk :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (p : FieldValuedPoint X),
    base (mk p) = p.structureHom default)

#check (AlgebraicGeometry.AlgebraicSpace.Points.base_map :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X),
    base (map f x) = base x)

end Points

#check (AlgebraicGeometry.AlgebraicSpace.fieldPointsToPoints :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {K : Type u} [Field K]
    (σ : Spec (.of K) ⟶ S) (p : ofOver (Over.mk σ) ⟶ X),
    Points X)

#check (AlgebraicGeometry.AlgebraicSpace.fieldPointsToPoints_eq :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {K : Type u}
    [Field K] (σ : Spec (.of K) ⟶ S) (p : ofOver (Over.mk σ) ⟶ X),
    fieldPointsToPoints σ p = Points.mk (FieldValuedPoint.of K σ p))

#check (AlgebraicGeometry.AlgebraicSpace.fieldPointsToPoints_base :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {K : Type u}
    [Field K] (σ : Spec (.of K) ⟶ S) (p : ofOver (Over.mk σ) ⟶ X),
    Points.base (fieldPointsToPoints σ p) = σ default)

#check (AlgebraicGeometry.AlgebraicSpace.pullbackFieldPoints :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {K : Type u} [Field K] (σ : Spec (.of K) ⟶ S),
    Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.pullbackFieldPoints_condition :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {K : Type u} [Field K] (σ : Spec (.of K) ⟶ S)
    (p : pullbackFieldPoints f σ),
    Points.map f p.1.1 = fieldPointsToPoints σ p.1.2)

#check (AlgebraicGeometry.AlgebraicSpace.toPullbackFieldPoints :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {K : Type u} [Field K] (σ : Spec (.of K) ⟶ S) (p : ofOver (Over.mk σ) ⟶ X),
    pullbackFieldPoints f σ)

#check (AlgebraicGeometry.AlgebraicSpace.toPullbackFieldPoints_apply :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {K : Type u} [Field K] (σ : Spec (.of K) ⟶ S)
    (p : ofOver (Over.mk σ) ⟶ X),
    (toPullbackFieldPoints f σ p).1 = (fieldPointsToPoints σ p, p ≫ f))

#check (AlgebraicGeometry.AlgebraicSpace.toPullbackFieldPoints_fst :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {K : Type u} [Field K] (σ : Spec (.of K) ⟶ S)
    (p : ofOver (Over.mk σ) ⟶ X),
    (toPullbackFieldPoints f σ p).1.1 = fieldPointsToPoints σ p)

#check (AlgebraicGeometry.AlgebraicSpace.toPullbackFieldPoints_snd :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {K : Type u} [Field K] (σ : Spec (.of K) ⟶ S)
    (p : ofOver (Over.mk σ) ⟶ X),
    (toPullbackFieldPoints f σ p).1.2 = p ≫ f)

end AlgebraicGeometry.AlgebraicSpace
