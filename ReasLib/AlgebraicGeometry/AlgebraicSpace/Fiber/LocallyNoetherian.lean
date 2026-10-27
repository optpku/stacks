/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-!
# Local Noetherianity of fibres of algebraic spaces

Residue-field fibres along étale scheme charts are locally Noetherian at a
point exactly when a field-valued representative has locally Noetherian fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The fibre of `f` over the residue-field point of an étale scheme chart of `Y`. -/
def residueFiberOver {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (a : ofOver V ⟶ Y) (v : V.left) : AlgebraicSpace S :=
  fieldFiber f ((FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v)).map a)

/-- `residueFiberOver f a v` is the fibre of `f` over the image of the residue-field
point of `v`. -/
theorem residueFiberOver_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (a : ofOver V ⟶ Y) (v : V.left) :
    residueFiberOver f a v =
      fieldFiber f
        ((FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v)).map a) :=
  rfl

/-- The residue-field point of a scheme chart, mapped to `Y`, represents the image
point `Points.mapOfOver a v`. -/
theorem residueFiberOver_mk {S : Scheme.{u}} {Y : AlgebraicSpace S} {V : Over S}
    (a : ofOver V ⟶ Y) (v : V.left) :
    Points.mk
        ((FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v)).map a) =
      Points.mapOfOver a v :=
  rfl

namespace LocallyNoetherianFiber

/-- There exist a scheme `V` over `S`, an étale morphism `a : ofOver V ⟶ Y`, and a
point `v` of `V` mapping to `y` such that `residueFiberOver f a v` is locally
Noetherian. -/
def existsEtale {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (y : Points Y) : Prop :=
  ∃ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left),
    Etale a ∧ Points.mapOfOver a v = y ∧
      IsLocallyNoetherian (residueFiberOver f a v)

/-- `existsEtale f y` unpacks as existence of an étale scheme chart through `y`
whose residue-field fibre is locally Noetherian. -/
theorem existsEtale_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (y : Points Y) :
    existsEtale f y ↔
      ∃ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left),
        Etale a ∧ Points.mapOfOver a v = y ∧
          IsLocallyNoetherian (residueFiberOver f a v) :=
  Iff.rfl

namespace existsEtale

/-- An étale scheme chart through `y` with locally Noetherian residue-field fibre
witnesses `existsEtale f y`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {y : Points Y}
    {V : Over S} (a : ofOver V ⟶ Y) (v : V.left) (ha : Etale a)
    (hv : Points.mapOfOver a v = y)
    (hN : IsLocallyNoetherian (residueFiberOver f a v)) :
    existsEtale f y :=
  ⟨V, a, v, ha, hv, hN⟩

/-- `existsEtale f y` supplies an étale scheme chart through `y` whose residue-field
fibre is locally Noetherian. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {y : Points Y}
    (h : existsEtale f y) :
    ∃ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left),
      Etale a ∧ Points.mapOfOver a v = y ∧
        IsLocallyNoetherian (residueFiberOver f a v) :=
  h

end existsEtale

/-- Every étale morphism from a scheme through `y` has locally Noetherian
residue-field fibre. -/
def forallEtale {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (y : Points Y) : Prop :=
  ∀ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left),
    Etale a → Points.mapOfOver a v = y →
      IsLocallyNoetherian (residueFiberOver f a v)

/-- `forallEtale f y` unpacks as local Noetherianity of the residue-field fibre on
every étale scheme chart through `y`. -/
theorem forallEtale_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (y : Points Y) :
    forallEtale f y ↔
      ∀ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left),
        Etale a → Points.mapOfOver a v = y →
          IsLocallyNoetherian (residueFiberOver f a v) :=
  Iff.rfl

namespace forallEtale

/-- The universal étale-chart condition witnesses `forallEtale f y`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {y : Points Y}
    (h : ∀ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left),
      Etale a → Points.mapOfOver a v = y →
        IsLocallyNoetherian (residueFiberOver f a v)) :
    forallEtale f y :=
  h

/-- If `forallEtale f y`, then every étale scheme chart through `y` has locally
Noetherian residue-field fibre. -/
theorem apply {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {y : Points Y}
    (h : forallEtale f y) {V : Over S} (a : ofOver V ⟶ Y) (v : V.left)
    (ha : Etale a) (hv : Points.mapOfOver a v = y) :
    IsLocallyNoetherian (residueFiberOver f a v) :=
  h V a v ha hv

end forallEtale

/-- There exists a field-valued point of `Y` representing `y` whose fibre under
`f` is locally Noetherian. -/
def existsField {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (y : Points Y) : Prop :=
  ∃ p : FieldValuedPoint Y, Points.mk p = y ∧ IsLocallyNoetherian (fieldFiber f p)

/-- `existsField f y` unpacks as existence of a field-valued representative of `y`
with locally Noetherian fibre. -/
theorem existsField_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (y : Points Y) :
    existsField f y ↔
      ∃ p : FieldValuedPoint Y,
        Points.mk p = y ∧ IsLocallyNoetherian (fieldFiber f p) :=
  Iff.rfl

namespace existsField

/-- A field-valued representative of `y` with locally Noetherian fibre witnesses
`existsField f y`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {y : Points Y}
    (p : FieldValuedPoint Y) (hp : Points.mk p = y)
    (hN : IsLocallyNoetherian (fieldFiber f p)) : existsField f y :=
  ⟨p, hp, hN⟩

/-- `existsField f y` supplies a field-valued representative of `y` with locally
Noetherian fibre. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {y : Points Y}
    (h : existsField f y) :
    ∃ p : FieldValuedPoint Y, Points.mk p = y ∧ IsLocallyNoetherian (fieldFiber f p) :=
  h

/-- A morphism `Spec(k) ⟶ Y` over `S` representing `y` with locally Noetherian
fibre witnesses `existsField f y`. -/
theorem of_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {y : Points Y}
    (k : Type u) [Field k] (σ : Spec (.of k) ⟶ S) (g : ofOver (Over.mk σ) ⟶ Y)
    (hp : Points.mk (FieldValuedPoint.of k σ g) = y)
    (hN : IsLocallyNoetherian (fieldFiber f (FieldValuedPoint.of k σ g))) :
    existsField f y :=
  ⟨FieldValuedPoint.of k σ g, hp, hN⟩

end existsField

/-- `existsField f y` is equivalent to existence of a field `k` and a morphism
`Spec(k) ⟶ Y` over `S` representing `y` whose fibre is locally Noetherian. -/
theorem existsField_iff_specField {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (y : Points Y) :
    existsField f y ↔
      ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
        (g : ofOver (Over.mk σ) ⟶ Y),
        Points.mk (FieldValuedPoint.of k σ g) = y ∧
          IsLocallyNoetherian (fieldFiber f (FieldValuedPoint.of k σ g)) :=
  by
    constructor
    · show existsField f y → _
      rintro ⟨p, hp, hN⟩
      exact ⟨p.K, p.field, p.structureHom, p.hom, hp, hN⟩
    · show _ → existsField f y
      rintro ⟨k, hk, σ, g, hp, hN⟩
      exact ⟨FieldValuedPoint.of k σ g, hp, hN⟩

end LocallyNoetherianFiber

open LocallyNoetherianFiber

/-- Let `S` be a scheme, let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`, and let `y` be a point of `Points Y`. The following
are equivalent: there exist a scheme `V` over `S`, a point `v` of `V`, and an
étale morphism `a : ofOver V ⟶ Y` mapping `v` to `y` such that
`residueFiberOver f a v` is locally Noetherian; the same holds for every such
étale morphism; and there exists a field-valued point of `Y` representing `y`
such that `fieldFiber f p` is locally Noetherian. -/
@[stacks 0CUW]
theorem locallyNoetherianFiber_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (y : Points Y) :
    List.TFAE [existsEtale f y, forallEtale f y, existsField f y] :=
  sorry

/-- For a monomorphic field-valued representative of a point, local Noetherianity
of its fibre is equivalent to existence of a field-valued representative of that
point with locally Noetherian fibre. -/
@[stacks 0CUW]
theorem locallyNoetherianFiber_iff_of_mono {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (y : Points Y) (p₀ : FieldValuedPoint Y) [Mono p₀.hom]
    (hp₀ : Points.mk p₀ = y) :
    IsLocallyNoetherian (fieldFiber f p₀) ↔ existsField f y :=
  sorry

/-- The fibre of a morphism `f : X ⟶ Y` of algebraic spaces over a point `y` of
`Points Y` is locally Noetherian when some field-valued representative of `y`
has locally Noetherian fibre. -/
@[mk_iff]
class IsLocallyNoetherianFiber {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (y : Points Y) : Prop where
  /-- Some field-valued representative of `y` has locally Noetherian fibre. -/
  existsField : LocallyNoetherianFiber.existsField f y

/-- The fibre of `f` over `y` is locally Noetherian if and only if some étale
scheme chart through `y` has locally Noetherian residue-field fibre, every such
chart has locally Noetherian residue-field fibre, and some field-valued
representative of `y` has locally Noetherian fibre. -/
theorem isLocallyNoetherianFiber_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (y : Points Y) :
    IsLocallyNoetherianFiber f y ↔
      LocallyNoetherianFiber.existsEtale f y ∧
        LocallyNoetherianFiber.forallEtale f y ∧
          LocallyNoetherianFiber.existsField f y :=
  by
    constructor
    · show IsLocallyNoetherianFiber f y → _
      intro h
      exact ⟨((locallyNoetherianFiber_tfae f y).out 0 2).mpr h.existsField,
        ((locallyNoetherianFiber_tfae f y).out 1 2).mpr h.existsField, h.existsField⟩
    · show _ → IsLocallyNoetherianFiber f y
      intro h
      exact ⟨h.2.2⟩

/-- The fibre of `f` over `y` is locally Noetherian if and only if some étale
scheme chart through `y` has locally Noetherian residue-field fibre. -/
theorem isLocallyNoetherianFiber_iff_existsEtale {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y) :
    IsLocallyNoetherianFiber f y ↔ LocallyNoetherianFiber.existsEtale f y :=
  ⟨fun h ↦ ((locallyNoetherianFiber_tfae f y).out 0 2).mpr h.existsField,
    fun h ↦ ⟨((locallyNoetherianFiber_tfae f y).out 0 2).mp h⟩⟩

/-- The fibre of `f` over `y` is locally Noetherian if and only if every étale
scheme chart through `y` has locally Noetherian residue-field fibre. -/
theorem isLocallyNoetherianFiber_iff_forallEtale {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y) :
    IsLocallyNoetherianFiber f y ↔ LocallyNoetherianFiber.forallEtale f y :=
  ⟨fun h ↦ ((locallyNoetherianFiber_tfae f y).out 1 2).mpr h.existsField,
    fun h ↦ ⟨((locallyNoetherianFiber_tfae f y).out 1 2).mp h⟩⟩

/-- The fibre of `f` over `y` is locally Noetherian if and only if some
field-valued representative of `y` has locally Noetherian fibre. -/
theorem isLocallyNoetherianFiber_iff_existsField {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y) :
    IsLocallyNoetherianFiber f y ↔ LocallyNoetherianFiber.existsField f y :=
  ⟨fun h ↦ h.existsField, fun h ↦ ⟨h⟩⟩

namespace IsLocallyNoetherianFiber

/-- A field-valued representative with locally Noetherian fibre witnesses that
the fibre of `f` over `y` is locally Noetherian. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {y : Points Y}
    (h : LocallyNoetherianFiber.existsField f y) :
    IsLocallyNoetherianFiber f y :=
  ⟨h⟩

/-- If the fibre of `f` over `y` is locally Noetherian, then some field-valued
representative of `y` has locally Noetherian fibre. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (y : Points Y) [IsLocallyNoetherianFiber f y] :
    LocallyNoetherianFiber.existsField f y :=
  IsLocallyNoetherianFiber.existsField

end IsLocallyNoetherianFiber

/-- A morphism `f : X ⟶ Y` of algebraic spaces has locally Noetherian fibres
when the fibre of `f` over every point of `Points Y` is locally Noetherian. -/
@[mk_iff]
class LocallyNoetherianFibers {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- The fibre of `f` over every point of `Points Y` is locally Noetherian. -/
  fiber : ∀ y : Points Y, IsLocallyNoetherianFiber f y

/-- The fibres of `f` are locally Noetherian if and only if, at every point of
`Points Y`, some étale scheme chart has locally Noetherian residue-field fibre,
every such chart has locally Noetherian residue-field fibre, and some
field-valued representative has locally Noetherian fibre. -/
theorem locallyNoetherianFibers_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    LocallyNoetherianFibers f ↔
      (∀ y : Points Y, LocallyNoetherianFiber.existsEtale f y) ∧
        (∀ y : Points Y, LocallyNoetherianFiber.forallEtale f y) ∧
          (∀ y : Points Y, LocallyNoetherianFiber.existsField f y) :=
  by
    constructor
    · show LocallyNoetherianFibers f → _
      intro h
      exact ⟨fun y ↦ ((isLocallyNoetherianFiber_spec f y).mp (h.fiber y)).1,
        fun y ↦ ((isLocallyNoetherianFiber_spec f y).mp (h.fiber y)).2.1,
        fun y ↦ (h.fiber y).existsField⟩
    · show _ → LocallyNoetherianFibers f
      intro h
      exact ⟨fun y ↦ ⟨h.2.2 y⟩⟩

/-- If the fibres of `f` are locally Noetherian, then the fibre over any point
of the target is locally Noetherian. -/
instance IsLocallyNoetherianFiber.ofFibers {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} [h : LocallyNoetherianFibers f]
    {y : Points Y} : IsLocallyNoetherianFiber f y :=
  h.fiber y

namespace LocallyNoetherianFibers

/-- The fibres of `f` are locally Noetherian if and only if, at every target
point, some field-valued representative has locally Noetherian fibre and every
étale scheme chart has locally Noetherian residue-field fibre. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    LocallyNoetherianFibers f ↔
      (∀ y : Points Y, LocallyNoetherianFiber.existsField f y) ∧
        (∀ y : Points Y, LocallyNoetherianFiber.forallEtale f y) :=
  by
    constructor
    · show LocallyNoetherianFibers f → _
      intro h
      exact ⟨fun y ↦ (h.fiber y).existsField,
        fun y ↦ (isLocallyNoetherianFiber_iff_forallEtale f y).mp (h.fiber y)⟩
    · show _ → LocallyNoetherianFibers f
      intro h
      exact ⟨fun y ↦ ⟨h.1 y⟩⟩

/-- The identity morphism of an algebraic space has locally Noetherian fibres. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    LocallyNoetherianFibers (𝟙 X) :=
  by
    constructor
    intro y
    refine Quotient.inductionOn y ?_
    intro p
    refine ⟨⟨p, rfl, ?_⟩⟩
    let q := fieldFiberToSpec (𝟙 X) p
    letI : IsIso q := (fieldFiber_isPullback (𝟙 X) p).isIso_snd_of_isIso
    let e₀ : fieldFiber (𝟙 X) p ≅ ofOver p.overObj := asIso q
    let e : (fieldFiber (𝟙 X) p).functorOfPoints ≅ yoneda.obj p.overObj :=
      { hom := e₀.hom
        inv := e₀.inv
        hom_inv_id := e₀.hom_inv_id
        inv_hom_id := e₀.inv_hom_id }
    let j := e.inv
    letI : IsIso j := e.isIso_inv
    letI : AlgebraicGeometry.IsLocallyNoetherian p.overObj.left := by
      change AlgebraicGeometry.IsLocallyNoetherian (Spec (.of p.K))
      have : IsNoetherianRing (CommRingCat.of p.K) := inferInstanceAs (IsNoetherianRing p.K)
      infer_instance
    refine ⟨⟨p.overObj, j, ?_, ?_, inferInstance⟩⟩
    · show (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf j
      refine ⟨Functor.relativelyRepresentable.of_isIso yoneda j, ?_⟩
      intro A B g fst snd h
      have : IsIso (yoneda.map snd) := h.isIso_snd_of_isIso
      have : IsIso snd := isIso_of_reflects_iso snd yoneda
      have : IsIso snd.left := inferInstanceAs (IsIso ((Over.forget S).map snd))
      change AlgebraicGeometry.Etale snd.left
      infer_instance
    · show Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) j
      infer_instance

end LocallyNoetherianFibers

end AlgebraicGeometry.AlgebraicSpace
