/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.LocallyNoetherian

/-!
# Relative weak association along fibres

Weak association of a quasi-coherent module to a point of the source of a
morphism of algebraic spaces, measured on residue-field fibres, étale charts of
the fibre product, and field-valued fibres.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.RelativeWeakAss

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The restriction of an `𝒪_X`-module to the fibre of `f` over a field-valued
point of `Y`. -/
def fiberModule (f : X ⟶ Y) (p : FieldValuedPoint Y) (F : X.Modules) :
    (fieldFiber f p).Modules :=
  (pullback (fieldFiberι f p)).obj F

/-- `fiberModule f p F` is the module pullback of `F` along `fieldFiberι f p`. -/
theorem fiberModule_eq (f : X ⟶ Y) (p : FieldValuedPoint Y) (F : X.Modules) :
    fiberModule f p F = (pullback (fieldFiberι f p)).obj F :=
  rfl

/-- The projection of a residue-field fibre to the source. -/
def residueFiberι (f : X ⟶ Y) {V : Over S} (a : ofOver V ⟶ Y) (v : V.left) :
    residueFiberOver f a v ⟶ X :=
  fieldFiberι f ((FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v)).map a)

/-- `residueFiberι f a v` is the fibre projection of the residue-field point of
`v`, mapped to `Y`. -/
theorem residueFiberι_eq (f : X ⟶ Y) {V : Over S} (a : ofOver V ⟶ Y) (v : V.left) :
    residueFiberι f a v =
      fieldFiberι f
        ((FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v)).map a) :=
  rfl

/-- The restriction of an `𝒪_X`-module to the residue-field fibre of `f` along an
étale scheme chart of `Y`. -/
def residueFiberModule (f : X ⟶ Y) (F : X.Modules) {V : Over S}
    (a : ofOver V ⟶ Y) (v : V.left) : (residueFiberOver f a v).Modules :=
  fiberModule f ((FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v)).map a) F

/-- `residueFiberModule f F a v` is `fiberModule` of the residue-field point of
`v`, mapped to `Y`. -/
theorem residueFiberModule_eq (f : X ⟶ Y) (F : X.Modules) {V : Over S}
    (a : ofOver V ⟶ Y) (v : V.left) :
    residueFiberModule f F a v =
      fiberModule f
        ((FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v)).map a) F :=
  rfl

/-- The composite `U → X ×_Y V → X`. -/
def chartToSource (f : X ⟶ Y) {V U : Over S} {a : ofOver V ⟶ Y}
    (b : ofOver U ⟶ Limits.pullback f a) : ofOver U ⟶ X :=
  b ≫ Limits.pullback.fst f a

/-- `chartToSource f b` is postcomposition of `b` with the first projection of
`X ×_Y V`. -/
theorem chartToSource_eq (f : X ⟶ Y) {V U : Over S} {a : ofOver V ⟶ Y}
    (b : ofOver U ⟶ Limits.pullback f a) :
    chartToSource f b = b ≫ Limits.pullback.fst f a :=
  rfl

/-- The composite `U → X ×_Y V → V`. -/
def chartToTarget (f : X ⟶ Y) {V U : Over S} {a : ofOver V ⟶ Y}
    (b : ofOver U ⟶ Limits.pullback f a) : ofOver U ⟶ ofOver V :=
  b ≫ Limits.pullback.snd f a

/-- `chartToTarget f b` is postcomposition of `b` with the second projection of
`X ×_Y V`. -/
theorem chartToTarget_eq (f : X ⟶ Y) {V U : Over S} {a : ofOver V ⟶ Y}
    (b : ofOver U ⟶ Limits.pullback f a) :
    chartToTarget f b = b ≫ Limits.pullback.snd f a :=
  rfl

/-- The residue-field fibre `U_v` of an étale chart `U → X ×_Y V`. -/
def chartFiber (f : X ⟶ Y) {V U : Over S} {a : ofOver V ⟶ Y}
    (b : ofOver U ⟶ Limits.pullback f a) (v : V.left) : AlgebraicSpace S :=
  fieldFiber (chartToTarget f b)
    (FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v))

/-- `chartFiber f b v` is the fibre of `U → V` over the residue-field point of
`v`. -/
theorem chartFiber_eq (f : X ⟶ Y) {V U : Over S} {a : ofOver V ⟶ Y}
    (b : ofOver U ⟶ Limits.pullback f a) (v : V.left) :
    chartFiber f b v =
      fieldFiber (chartToTarget f b)
        (FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v)) :=
  rfl

/-- The projection of `U_v` to `U`. -/
def chartFiberι (f : X ⟶ Y) {V U : Over S} {a : ofOver V ⟶ Y}
    (b : ofOver U ⟶ Limits.pullback f a) (v : V.left) :
    chartFiber f b v ⟶ ofOver U :=
  fieldFiberι (chartToTarget f b)
    (FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v))

/-- `chartFiberι f b v` is the fibre projection of `U_v` to `U`. -/
theorem chartFiberι_eq (f : X ⟶ Y) {V U : Over S} {a : ofOver V ⟶ Y}
    (b : ofOver U ⟶ Limits.pullback f a) (v : V.left) :
    chartFiberι f b v =
      fieldFiberι (chartToTarget f b)
        (FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v)) :=
  rfl

/-- The restriction of an `𝒪_X`-module to the residue-field fibre `U_v`. -/
def chartFiberModule (f : X ⟶ Y) (F : X.Modules) {V U : Over S} {a : ofOver V ⟶ Y}
    (b : ofOver U ⟶ Limits.pullback f a) (v : V.left) :
    (chartFiber f b v).Modules :=
  (pullback (chartFiberι f b v ≫ chartToSource f b)).obj F

/-- `chartFiberModule f F b v` is the pullback of `F` along `U_v → X`. -/
theorem chartFiberModule_eq (f : X ⟶ Y) (F : X.Modules) {V U : Over S}
    {a : ofOver V ⟶ Y} (b : ofOver U ⟶ Limits.pullback f a) (v : V.left) :
    chartFiberModule f F b v =
      (pullback (chartFiberι f b v ≫ chartToSource f b)).obj F :=
  rfl

/-- There exist an étale scheme chart of `Y` through `f(x)` and a lift of `x` on
the residue-field fibre which is weakly associated to the restricted module. -/
def existsEtale (f : X ⟶ Y) (F : X.Modules) (x : Points X) : Prop :=
  ∃ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left) (x' : Points (residueFiberOver f a v)),
    Etale a ∧ Points.mapOfOver a v = Points.map f x ∧
      Points.map (residueFiberι f a v) x' = x ∧
      x' ∈ (residueFiberModule f F a v).weakAss

/-- The existential étale-chart condition is equivalent to existence of a target
chart through the image point with a weakly associated residue-field fibre lift. -/
theorem existsEtale_iff (f : X ⟶ Y) (F : X.Modules) (x : Points X) :
    existsEtale f F x ↔
      ∃ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left)
          (x' : Points (residueFiberOver f a v)),
        Etale a ∧ Points.mapOfOver a v = Points.map f x ∧
          Points.map (residueFiberι f a v) x' = x ∧
          x' ∈ (residueFiberModule f F a v).weakAss :=
  Iff.rfl

namespace existsEtale

/-- An étale residue-field fibre lift in the weakly associated locus witnesses
`existsEtale`. -/
theorem of (f : X ⟶ Y) (F : X.Modules) {x : Points X} {V : Over S}
    (a : ofOver V ⟶ Y) (v : V.left) (x' : Points (residueFiberOver f a v))
    (ha : Etale a) (hv : Points.mapOfOver a v = Points.map f x)
    (hx' : Points.map (residueFiberι f a v) x' = x)
    (h : x' ∈ (residueFiberModule f F a v).weakAss) :
    existsEtale f F x :=
  ⟨V, a, v, x', ha, hv, hx', h⟩

/-- `existsEtale` supplies an étale residue-field fibre lift in the weakly
associated locus. -/
theorem spec (f : X ⟶ Y) (F : X.Modules) {x : Points X} (h : existsEtale f F x) :
    ∃ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left)
        (x' : Points (residueFiberOver f a v)),
      Etale a ∧ Points.mapOfOver a v = Points.map f x ∧
        Points.map (residueFiberι f a v) x' = x ∧
        x' ∈ (residueFiberModule f F a v).weakAss :=
  h

end existsEtale

/-- Every étale scheme chart of `Y` through `f(x)` has every lift of `x` on the
residue-field fibre weakly associated to the restricted module. -/
def forallEtale (f : X ⟶ Y) (F : X.Modules) (x : Points X) : Prop :=
  ∀ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left) (x' : Points (residueFiberOver f a v)),
    Etale a → Points.mapOfOver a v = Points.map f x →
      Points.map (residueFiberι f a v) x' = x →
        x' ∈ (residueFiberModule f F a v).weakAss

/-- The universal étale-chart condition is equivalent to weak association of every
residue-field fibre lift on every target chart through the image point. -/
theorem forallEtale_iff (f : X ⟶ Y) (F : X.Modules) (x : Points X) :
    forallEtale f F x ↔
      ∀ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left)
          (x' : Points (residueFiberOver f a v)),
        Etale a → Points.mapOfOver a v = Points.map f x →
          Points.map (residueFiberι f a v) x' = x →
            x' ∈ (residueFiberModule f F a v).weakAss :=
  Iff.rfl

namespace forallEtale

/-- The universal étale residue-field condition witnesses `forallEtale`. -/
theorem of (f : X ⟶ Y) (F : X.Modules) {x : Points X}
    (h : ∀ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left)
        (x' : Points (residueFiberOver f a v)),
      Etale a → Points.mapOfOver a v = Points.map f x →
        Points.map (residueFiberι f a v) x' = x →
          x' ∈ (residueFiberModule f F a v).weakAss) :
    forallEtale f F x :=
  h

/-- If `forallEtale` holds, every residue-field fibre lift of `x` is weakly
associated to the restricted module. -/
theorem apply (f : X ⟶ Y) (F : X.Modules) {x : Points X} (h : forallEtale f F x)
    {V : Over S} (a : ofOver V ⟶ Y) (v : V.left)
    (x' : Points (residueFiberOver f a v)) (ha : Etale a)
    (hv : Points.mapOfOver a v = Points.map f x)
    (hx' : Points.map (residueFiberι f a v) x' = x) :
    x' ∈ (residueFiberModule f F a v).weakAss :=
  h V a v x' ha hv hx'

end forallEtale

/-- There exist étale charts `V → Y` and `U → X ×_Y V` through `f(x)` such that a
point of `U_v` lifting `u` is weakly associated to the restriction of `F`. -/
def existsOverPullback (f : X ⟶ Y) (F : X.Modules) (x : Points X) : Prop :=
  ∃ (V : Over S) (a : ofOver V ⟶ Y) (U : Over S) (b : ofOver U ⟶ Limits.pullback f a)
      (v : V.left) (u : U.left) (t : Points (chartFiber f b v)),
    Etale a ∧ Etale b ∧ Points.mapOfOver a v = Points.map f x ∧
      Points.map (chartToSource f b) (ofOver.pointsEquiv U u) = x ∧
      Points.map (chartToTarget f b) (ofOver.pointsEquiv U u) = ofOver.pointsEquiv V v ∧
      Points.map (chartFiberι f b v) t = ofOver.pointsEquiv U u ∧
      t ∈ (chartFiberModule f F b v).weakAss

/-- The existential fibre-product chart condition is equivalent to existence of
étale charts and related points with a weakly associated lift on the chart fibre. -/
theorem existsOverPullback_iff (f : X ⟶ Y) (F : X.Modules) (x : Points X) :
    existsOverPullback f F x ↔
      ∃ (V : Over S) (a : ofOver V ⟶ Y) (U : Over S)
          (b : ofOver U ⟶ Limits.pullback f a) (v : V.left) (u : U.left)
          (t : Points (chartFiber f b v)),
        Etale a ∧ Etale b ∧ Points.mapOfOver a v = Points.map f x ∧
          Points.map (chartToSource f b) (ofOver.pointsEquiv U u) = x ∧
          Points.map (chartToTarget f b) (ofOver.pointsEquiv U u) =
            ofOver.pointsEquiv V v ∧
          Points.map (chartFiberι f b v) t = ofOver.pointsEquiv U u ∧
          t ∈ (chartFiberModule f F b v).weakAss :=
  Iff.rfl

namespace existsOverPullback

/-- An étale fibre-product chart with a weakly associated lift to `U_v` witnesses
`existsOverPullback`. -/
theorem of (f : X ⟶ Y) (F : X.Modules) {x : Points X} {V U : Over S}
    (a : ofOver V ⟶ Y) (b : ofOver U ⟶ Limits.pullback f a) (v : V.left) (u : U.left)
    (t : Points (chartFiber f b v)) (ha : Etale a) (hb : Etale b)
    (hv : Points.mapOfOver a v = Points.map f x)
    (hx : Points.map (chartToSource f b) (ofOver.pointsEquiv U u) = x)
    (hu : Points.map (chartToTarget f b) (ofOver.pointsEquiv U u) = ofOver.pointsEquiv V v)
    (ht : Points.map (chartFiberι f b v) t = ofOver.pointsEquiv U u)
    (h : t ∈ (chartFiberModule f F b v).weakAss) :
    existsOverPullback f F x :=
  ⟨V, a, U, b, v, u, t, ha, hb, hv, hx, hu, ht, h⟩

/-- `existsOverPullback` supplies étale fibre-product charts with a weakly
associated lift to `U_v`. -/
theorem spec (f : X ⟶ Y) (F : X.Modules) {x : Points X}
    (h : existsOverPullback f F x) :
    ∃ (V : Over S) (a : ofOver V ⟶ Y) (U : Over S)
        (b : ofOver U ⟶ Limits.pullback f a) (v : V.left) (u : U.left)
        (t : Points (chartFiber f b v)),
      Etale a ∧ Etale b ∧ Points.mapOfOver a v = Points.map f x ∧
        Points.map (chartToSource f b) (ofOver.pointsEquiv U u) = x ∧
        Points.map (chartToTarget f b) (ofOver.pointsEquiv U u) =
          ofOver.pointsEquiv V v ∧
        Points.map (chartFiberι f b v) t = ofOver.pointsEquiv U u ∧
        t ∈ (chartFiberModule f F b v).weakAss :=
  h

end existsOverPullback

/-- For every pair of étale charts `V → Y` and `U → X ×_Y V`, every related
lift of a point over `x` to `U_v` is weakly associated to the restriction of `F`. -/
def forallOverPullback (f : X ⟶ Y) (F : X.Modules) (x : Points X) : Prop :=
  ∀ (V : Over S) (a : ofOver V ⟶ Y) (U : Over S) (b : ofOver U ⟶ Limits.pullback f a)
    (v : V.left) (u : U.left) (t : Points (chartFiber f b v)),
    Etale a → Etale b → Points.mapOfOver a v = Points.map f x →
      Points.map (chartToSource f b) (ofOver.pointsEquiv U u) = x →
      Points.map (chartToTarget f b) (ofOver.pointsEquiv U u) = ofOver.pointsEquiv V v →
      Points.map (chartFiberι f b v) t = ofOver.pointsEquiv U u →
        t ∈ (chartFiberModule f F b v).weakAss

/-- The universal fibre-product chart condition is equivalent to weak association
of every related lift on the residue-field fibre of every pair of étale charts. -/
theorem forallOverPullback_iff (f : X ⟶ Y) (F : X.Modules) (x : Points X) :
    forallOverPullback f F x ↔
      ∀ (V : Over S) (a : ofOver V ⟶ Y) (U : Over S)
        (b : ofOver U ⟶ Limits.pullback f a) (v : V.left) (u : U.left)
        (t : Points (chartFiber f b v)),
        Etale a → Etale b → Points.mapOfOver a v = Points.map f x →
          Points.map (chartToSource f b) (ofOver.pointsEquiv U u) = x →
          Points.map (chartToTarget f b) (ofOver.pointsEquiv U u) =
            ofOver.pointsEquiv V v →
          Points.map (chartFiberι f b v) t = ofOver.pointsEquiv U u →
            t ∈ (chartFiberModule f F b v).weakAss :=
  Iff.rfl

namespace forallOverPullback

/-- The universal fibre-product chart condition witnesses `forallOverPullback`. -/
theorem of (f : X ⟶ Y) (F : X.Modules) {x : Points X}
    (h : ∀ (V : Over S) (a : ofOver V ⟶ Y) (U : Over S)
        (b : ofOver U ⟶ Limits.pullback f a) (v : V.left) (u : U.left)
        (t : Points (chartFiber f b v)),
      Etale a → Etale b → Points.mapOfOver a v = Points.map f x →
        Points.map (chartToSource f b) (ofOver.pointsEquiv U u) = x →
        Points.map (chartToTarget f b) (ofOver.pointsEquiv U u) =
          ofOver.pointsEquiv V v →
        Points.map (chartFiberι f b v) t = ofOver.pointsEquiv U u →
          t ∈ (chartFiberModule f F b v).weakAss) :
    forallOverPullback f F x :=
  h

/-- If `forallOverPullback` holds, every related lift to `U_v` is weakly
associated to the restricted module. -/
theorem apply (f : X ⟶ Y) (F : X.Modules) {x : Points X}
    (h : forallOverPullback f F x) {V U : Over S} (a : ofOver V ⟶ Y)
    (b : ofOver U ⟶ Limits.pullback f a) (v : V.left) (u : U.left)
    (t : Points (chartFiber f b v)) (ha : Etale a) (hb : Etale b)
    (hv : Points.mapOfOver a v = Points.map f x)
    (hx : Points.map (chartToSource f b) (ofOver.pointsEquiv U u) = x)
    (hu : Points.map (chartToTarget f b) (ofOver.pointsEquiv U u) = ofOver.pointsEquiv V v)
    (ht : Points.map (chartFiberι f b v) t = ofOver.pointsEquiv U u) :
    t ∈ (chartFiberModule f F b v).weakAss :=
  h V a U b v u t ha hb hv hx hu ht

end forallOverPullback

/-- There exist a field-valued representative of `f(x)` and a lift of `x` on the
corresponding fibre which is weakly associated to the restricted module. -/
def existsField (f : X ⟶ Y) (F : X.Modules) (x : Points X) : Prop :=
  ∃ (p : FieldValuedPoint Y) (t : Points (fieldFiber f p)),
    Points.mk p = Points.map f x ∧ Points.map (fieldFiberι f p) t = x ∧
      t ∈ (fiberModule f p F).weakAss

/-- The field-valued condition is equivalent to existence of a representative of
the image point with a weakly associated fibre lift of the source point. -/
theorem existsField_iff (f : X ⟶ Y) (F : X.Modules) (x : Points X) :
    existsField f F x ↔
      ∃ (p : FieldValuedPoint Y) (t : Points (fieldFiber f p)),
        Points.mk p = Points.map f x ∧ Points.map (fieldFiberι f p) t = x ∧
          t ∈ (fiberModule f p F).weakAss :=
  Iff.rfl

namespace existsField

/-- A field-valued fibre lift in the weakly associated locus witnesses
`existsField`. -/
theorem of (f : X ⟶ Y) (F : X.Modules) {x : Points X} (p : FieldValuedPoint Y)
    (t : Points (fieldFiber f p)) (hp : Points.mk p = Points.map f x)
    (ht : Points.map (fieldFiberι f p) t = x) (h : t ∈ (fiberModule f p F).weakAss) :
    existsField f F x :=
  ⟨p, t, hp, ht, h⟩

/-- `existsField` supplies a field-valued fibre lift in the weakly associated
locus. -/
theorem spec (f : X ⟶ Y) (F : X.Modules) {x : Points X} (h : existsField f F x) :
    ∃ (p : FieldValuedPoint Y) (t : Points (fieldFiber f p)),
      Points.mk p = Points.map f x ∧ Points.map (fieldFiberι f p) t = x ∧
        t ∈ (fiberModule f p F).weakAss :=
  h

/-- A morphism `Spec(k) ⟶ Y` over `S` representing `f(x)` with a weakly
associated fibre lift witnesses `existsField`. -/
theorem of_spec (f : X ⟶ Y) (F : X.Modules) {x : Points X} (k : Type u) [Field k]
    (σ : Spec (.of k) ⟶ S) (g : ofOver (Over.mk σ) ⟶ Y)
    (t : Points (fieldFiber f (FieldValuedPoint.of k σ g)))
    (hp : Points.mk (FieldValuedPoint.of k σ g) = Points.map f x)
    (ht : Points.map (fieldFiberι f (FieldValuedPoint.of k σ g)) t = x)
    (h : t ∈ (fiberModule f (FieldValuedPoint.of k σ g) F).weakAss) :
    existsField f F x :=
  ⟨FieldValuedPoint.of k σ g, t, hp, ht, h⟩

end existsField

/-- `existsField` is equivalent to existence of a field `k` and a morphism
`Spec(k) ⟶ Y` over `S` representing `f(x)` with a weakly associated fibre lift of
`x`. -/
theorem existsField_iff_specField (f : X ⟶ Y) (F : X.Modules) (x : Points X) :
    existsField f F x ↔
      ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S) (g : ofOver (Over.mk σ) ⟶ Y)
        (t : Points (fieldFiber f (FieldValuedPoint.of k σ g))),
        Points.mk (FieldValuedPoint.of k σ g) = Points.map f x ∧
          Points.map (fieldFiberι f (FieldValuedPoint.of k σ g)) t = x ∧
          t ∈ (fiberModule f (FieldValuedPoint.of k σ g) F).weakAss := by
  constructor
  · rintro ⟨p, t, hp, ht, h⟩
    exact ⟨p.K, p.field, p.structureHom, p.hom, t, hp, ht, h⟩
  · rintro ⟨k, hk, σ, g, t, hp, ht, h⟩
    exact ⟨FieldValuedPoint.of k σ g, t, hp, ht, h⟩

/-- The unique lift of `x` to the fibre over a monomorphic field-valued
representative of `f(x)` is weakly associated to the restricted module. -/
def ofMono (f : X ⟶ Y) (F : X.Modules) (x : Points X) (p₀ : FieldValuedPoint Y)
    [Mono p₀.hom] : Prop :=
  ∃ t : Points (fieldFiber f p₀),
    Points.map (fieldFiberι f p₀) t = x ∧ t ∈ (fiberModule f p₀ F).weakAss

/-- The monomorphic-fibre condition is equivalent to existence of a weakly
associated fibre point mapping to the source point. -/
theorem ofMono_iff (f : X ⟶ Y) (F : X.Modules) (x : Points X)
    (p₀ : FieldValuedPoint Y) [Mono p₀.hom] :
    ofMono f F x p₀ ↔
      ∃ t : Points (fieldFiber f p₀),
        Points.map (fieldFiberι f p₀) t = x ∧ t ∈ (fiberModule f p₀ F).weakAss :=
  Iff.rfl

namespace ofMono

/-- A weakly associated fibre lift over a monomorphic representative witnesses
`ofMono`. -/
theorem of (f : X ⟶ Y) (F : X.Modules) {x : Points X} (p₀ : FieldValuedPoint Y)
    [Mono p₀.hom] (t : Points (fieldFiber f p₀))
    (ht : Points.map (fieldFiberι f p₀) t = x) (h : t ∈ (fiberModule f p₀ F).weakAss) :
    ofMono f F x p₀ :=
  ⟨t, ht, h⟩

/-- `ofMono` supplies a weakly associated fibre lift over a monomorphic
representative. -/
theorem spec (f : X ⟶ Y) (F : X.Modules) {x : Points X} (p₀ : FieldValuedPoint Y)
    [Mono p₀.hom] (h : ofMono f F x p₀) :
    ∃ t : Points (fieldFiber f p₀),
      Points.map (fieldFiberι f p₀) t = x ∧ t ∈ (fiberModule f p₀ F).weakAss :=
  h

end ofMono

/-- There exist an étale scheme chart of `Y` through `f(x)` and a lift of `x` on
the residue-field fibre which is associated to the restricted module. -/
def existsEtaleAss (f : X ⟶ Y) (F : X.Modules) (x : Points X) : Prop :=
  ∃ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left) (x' : Points (residueFiberOver f a v)),
    Etale a ∧ Points.mapOfOver a v = Points.map f x ∧
      Points.map (residueFiberι f a v) x' = x ∧
      Modules.existsEtaleAss (residueFiberModule f F a v) x'

/-- The existential associated-point chart condition is equivalent to existence of
a target chart through the image point with an associated residue-field fibre lift. -/
theorem existsEtaleAss_iff (f : X ⟶ Y) (F : X.Modules) (x : Points X) :
    existsEtaleAss f F x ↔
      ∃ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left)
          (x' : Points (residueFiberOver f a v)),
        Etale a ∧ Points.mapOfOver a v = Points.map f x ∧
          Points.map (residueFiberι f a v) x' = x ∧
          Modules.existsEtaleAss (residueFiberModule f F a v) x' :=
  Iff.rfl

namespace existsEtaleAss

/-- An étale residue-field fibre lift associated to the restricted module
witnesses `existsEtaleAss`. -/
theorem of (f : X ⟶ Y) (F : X.Modules) {x : Points X} {V : Over S}
    (a : ofOver V ⟶ Y) (v : V.left) (x' : Points (residueFiberOver f a v))
    (ha : Etale a) (hv : Points.mapOfOver a v = Points.map f x)
    (hx' : Points.map (residueFiberι f a v) x' = x)
    (h : Modules.existsEtaleAss (residueFiberModule f F a v) x') :
    existsEtaleAss f F x :=
  ⟨V, a, v, x', ha, hv, hx', h⟩

/-- `existsEtaleAss` supplies an étale residue-field fibre lift associated to the
restricted module. -/
theorem spec (f : X ⟶ Y) (F : X.Modules) {x : Points X} (h : existsEtaleAss f F x) :
    ∃ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left)
        (x' : Points (residueFiberOver f a v)),
      Etale a ∧ Points.mapOfOver a v = Points.map f x ∧
        Points.map (residueFiberι f a v) x' = x ∧
        Modules.existsEtaleAss (residueFiberModule f F a v) x' :=
  h

end existsEtaleAss

/-- Every étale scheme chart of `Y` through `f(x)` has every lift of `x` on the
residue-field fibre associated to the restricted module. -/
def forallEtaleAss (f : X ⟶ Y) (F : X.Modules) (x : Points X) : Prop :=
  ∀ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left) (x' : Points (residueFiberOver f a v)),
    Etale a → Points.mapOfOver a v = Points.map f x →
      Points.map (residueFiberι f a v) x' = x →
        Modules.existsEtaleAss (residueFiberModule f F a v) x'

/-- The universal associated-point chart condition is equivalent to association of
every residue-field fibre lift on every target chart through the image point. -/
theorem forallEtaleAss_iff (f : X ⟶ Y) (F : X.Modules) (x : Points X) :
    forallEtaleAss f F x ↔
      ∀ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left)
          (x' : Points (residueFiberOver f a v)),
        Etale a → Points.mapOfOver a v = Points.map f x →
          Points.map (residueFiberι f a v) x' = x →
            Modules.existsEtaleAss (residueFiberModule f F a v) x' :=
  Iff.rfl

namespace forallEtaleAss

/-- The universal associated étale residue-field condition witnesses
`forallEtaleAss`. -/
theorem of (f : X ⟶ Y) (F : X.Modules) {x : Points X}
    (h : ∀ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left)
        (x' : Points (residueFiberOver f a v)),
      Etale a → Points.mapOfOver a v = Points.map f x →
        Points.map (residueFiberι f a v) x' = x →
          Modules.existsEtaleAss (residueFiberModule f F a v) x') :
    forallEtaleAss f F x :=
  h

/-- If `forallEtaleAss` holds, every residue-field fibre lift of `x` is associated
to the restricted module. -/
theorem apply (f : X ⟶ Y) (F : X.Modules) {x : Points X} (h : forallEtaleAss f F x)
    {V : Over S} (a : ofOver V ⟶ Y) (v : V.left)
    (x' : Points (residueFiberOver f a v)) (ha : Etale a)
    (hv : Points.mapOfOver a v = Points.map f x)
    (hx' : Points.map (residueFiberι f a v) x' = x) :
    Modules.existsEtaleAss (residueFiberModule f F a v) x' :=
  h V a v x' ha hv hx'

end forallEtaleAss

/-- There exist étale charts `V → Y` and `U → X ×_Y V` through `f(x)` such that a
point of `U_v` lifting `u` is associated to the restriction of `F`. -/
def existsOverPullbackAss (f : X ⟶ Y) (F : X.Modules) (x : Points X) : Prop :=
  ∃ (V : Over S) (a : ofOver V ⟶ Y) (U : Over S) (b : ofOver U ⟶ Limits.pullback f a)
      (v : V.left) (u : U.left) (t : Points (chartFiber f b v)),
    Etale a ∧ Etale b ∧ Points.mapOfOver a v = Points.map f x ∧
      Points.map (chartToSource f b) (ofOver.pointsEquiv U u) = x ∧
      Points.map (chartToTarget f b) (ofOver.pointsEquiv U u) = ofOver.pointsEquiv V v ∧
      Points.map (chartFiberι f b v) t = ofOver.pointsEquiv U u ∧
      Modules.existsEtaleAss (chartFiberModule f F b v) t

/-- The existential associated-point fibre-product condition is equivalent to
existence of étale charts and related points with an associated chart-fibre lift. -/
theorem existsOverPullbackAss_iff (f : X ⟶ Y) (F : X.Modules) (x : Points X) :
    existsOverPullbackAss f F x ↔
      ∃ (V : Over S) (a : ofOver V ⟶ Y) (U : Over S)
          (b : ofOver U ⟶ Limits.pullback f a) (v : V.left) (u : U.left)
          (t : Points (chartFiber f b v)),
        Etale a ∧ Etale b ∧ Points.mapOfOver a v = Points.map f x ∧
          Points.map (chartToSource f b) (ofOver.pointsEquiv U u) = x ∧
          Points.map (chartToTarget f b) (ofOver.pointsEquiv U u) =
            ofOver.pointsEquiv V v ∧
          Points.map (chartFiberι f b v) t = ofOver.pointsEquiv U u ∧
          Modules.existsEtaleAss (chartFiberModule f F b v) t :=
  Iff.rfl

/-- For every pair of étale charts `V → Y` and `U → X ×_Y V`, every related
lift of a point over `x` to `U_v` is associated to the restriction of `F`. -/
def forallOverPullbackAss (f : X ⟶ Y) (F : X.Modules) (x : Points X) : Prop :=
  ∀ (V : Over S) (a : ofOver V ⟶ Y) (U : Over S) (b : ofOver U ⟶ Limits.pullback f a)
    (v : V.left) (u : U.left) (t : Points (chartFiber f b v)),
    Etale a → Etale b → Points.mapOfOver a v = Points.map f x →
      Points.map (chartToSource f b) (ofOver.pointsEquiv U u) = x →
      Points.map (chartToTarget f b) (ofOver.pointsEquiv U u) = ofOver.pointsEquiv V v →
      Points.map (chartFiberι f b v) t = ofOver.pointsEquiv U u →
        Modules.existsEtaleAss (chartFiberModule f F b v) t

/-- The universal associated-point fibre-product condition is equivalent to
association of every related chart-fibre lift for every pair of étale charts. -/
theorem forallOverPullbackAss_iff (f : X ⟶ Y) (F : X.Modules) (x : Points X) :
    forallOverPullbackAss f F x ↔
      ∀ (V : Over S) (a : ofOver V ⟶ Y) (U : Over S)
        (b : ofOver U ⟶ Limits.pullback f a) (v : V.left) (u : U.left)
        (t : Points (chartFiber f b v)),
        Etale a → Etale b → Points.mapOfOver a v = Points.map f x →
          Points.map (chartToSource f b) (ofOver.pointsEquiv U u) = x →
          Points.map (chartToTarget f b) (ofOver.pointsEquiv U u) =
            ofOver.pointsEquiv V v →
          Points.map (chartFiberι f b v) t = ofOver.pointsEquiv U u →
            Modules.existsEtaleAss (chartFiberModule f F b v) t :=
  Iff.rfl

/-- The unique lift of `x` to the fibre over a monomorphic field-valued
representative of `f(x)` is associated to the restricted module. -/
def ofMonoAss (f : X ⟶ Y) (F : X.Modules) (x : Points X) (p₀ : FieldValuedPoint Y)
    [Mono p₀.hom] : Prop :=
  ∃ t : Points (fieldFiber f p₀),
    Points.map (fieldFiberι f p₀) t = x ∧ Modules.existsEtaleAss (fiberModule f p₀ F) t

/-- The monomorphic associated-point condition is equivalent to existence of an
associated fibre point mapping to the source point. -/
theorem ofMonoAss_iff (f : X ⟶ Y) (F : X.Modules) (x : Points X)
    (p₀ : FieldValuedPoint Y) [Mono p₀.hom] :
    ofMonoAss f F x p₀ ↔
      ∃ t : Points (fieldFiber f p₀),
        Points.map (fieldFiberι f p₀) t = x ∧
          Modules.existsEtaleAss (fiberModule f p₀ F) t :=
  Iff.rfl

/-- If the fibre of `f` over `f(x)` is locally Noetherian, then association and
weak association of the monomorphic fibre lift agree. -/
theorem ofMonoAss_iff_ofMono (f : X ⟶ Y) (F : X.Modules) [F.IsQuasicoherent]
    (x : Points X) (p₀ : FieldValuedPoint Y) [Mono p₀.hom]
    (hp₀ : Points.mk p₀ = Points.map f x)
    [IsLocallyNoetherianFiber f (Points.map f x)] :
    ofMonoAss f F x p₀ ↔ ofMono f F x p₀ := by
  letI : IsLocallyNoetherian (fieldFiber f p₀) :=
    (locallyNoetherianFiber_iff_of_mono f (Points.map f x) p₀ hp₀).mpr
      (IsLocallyNoetherianFiber.existsField (f := f) (y := Points.map f x))
  letI : (fiberModule f p₀ F).IsQuasicoherent :=
    Modules.pullback_isQuasicoherent (fieldFiberι f p₀) F
  rw [ofMonoAss_iff, ofMono_iff]
  refine exists_congr fun t => and_congr_right fun _ => ?_
  exact (Modules.existsEtaleAss_iff_existsEtaleWeakAss (fiberModule f p₀ F) t).trans
    (Modules.mem_weakAss_iff_existsEtaleWeakAss (fiberModule f p₀ F) t).symm

/-- For a quasi-coherent module, weak association of a fibre lift is equivalent
across existential and universal étale target charts, existential and universal
étale fibre-product charts, and existence of a field-valued fibre lift. -/
@[stacks 0CUZ]
theorem relativeWeakAss_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : X.Modules) [F.IsQuasicoherent] (x : Points X) :
    List.TFAE [existsEtale f F x, forallEtale f F x, existsOverPullback f F x,
      forallOverPullback f F x, existsField f F x] :=
  sorry

/-- For a monomorphic field-valued representative of the image point, weak
association of the unique fibre lift is equivalent to existence of a weakly
associated lift on a field-valued fibre. -/
@[stacks 0CUZ]
theorem relativeWeakAss_iff_of_mono {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : X.Modules) [F.IsQuasicoherent] (x : Points X)
    (p₀ : FieldValuedPoint Y) [Mono p₀.hom]
    (hp₀ : Points.mk p₀ = Points.map f x) :
    ofMono f F x p₀ ↔ existsField f F x :=
  sorry

/-- If the fibre over the image point is locally Noetherian, the weak-association
conditions on étale target and fibre-product charts are equivalent to their
associated-point versions and to existence of a weakly associated field-valued
fibre lift. -/
@[stacks 0CUZ]
theorem associatedPoints_fiber_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : X.Modules) [F.IsQuasicoherent] (x : Points X)
    [IsLocallyNoetherianFiber f (Points.map f x)] :
    List.TFAE [existsEtale f F x, forallEtale f F x, existsOverPullback f F x,
      forallOverPullback f F x, existsField f F x, existsEtaleAss f F x,
      forallEtaleAss f F x, existsOverPullbackAss f F x, forallOverPullbackAss f F x] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.RelativeWeakAss
