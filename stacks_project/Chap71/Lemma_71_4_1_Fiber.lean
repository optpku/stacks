module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap68.Lemma_68_18_6_Fibre

/-!
# Fibres of morphisms of algebraic spaces over field-valued points

The fibre of a morphism `f : X ⟶ Y` of algebraic spaces over a field-valued
point `p` of `Y` is the fibre product `fieldFiber f p = pullback f p.hom`.
Residue-field fibres along étale scheme charts are the special case of the
canonical residue-field point of the chart, mapped to `Y`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The projection of the fibre over a field-valued point to the source. -/
def fiberι {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (p : FieldValuedPoint Y) : fieldFiber f p ⟶ X :=
  pullback.fst f p.hom

/-- `fiberι f p` is the first projection of the fibre product. -/
theorem fiberι_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (p : FieldValuedPoint Y) : fiberι f p = pullback.fst f p.hom :=
  sorry

/-- The structure morphism of the fibre over a field-valued point to `Spec(p.K)`. -/
def fiberToSpec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (p : FieldValuedPoint Y) : fieldFiber f p ⟶ ofOver p.overObj :=
  pullback.snd f p.hom

/-- `fiberToSpec f p` is the second projection of the fibre product. -/
theorem fiberToSpec_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (p : FieldValuedPoint Y) : fiberToSpec f p = pullback.snd f p.hom :=
  sorry

/-- The fibre square of `f` over a field-valued point is a pullback square. -/
theorem isPullback_fiberOver {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (p : FieldValuedPoint Y) :
    IsPullback (fiberι f p) (fiberToSpec f p) f p.hom :=
  sorry

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
  sorry

/-- The residue-field point of a scheme chart, mapped to `Y`, represents the image
point `Points.mapOfOver a v`. -/
theorem residueFiberOver_mk {S : Scheme.{u}} {Y : AlgebraicSpace S} {V : Over S}
    (a : ofOver V ⟶ Y) (v : V.left) :
    Points.mk
        ((FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v)).map a) =
      Points.mapOfOver a v :=
  sorry

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
  sorry

namespace existsEtale

/-- An étale scheme chart through `y` with locally Noetherian residue-field fibre
witnesses `existsEtale f y`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {y : Points Y}
    {V : Over S} (a : ofOver V ⟶ Y) (v : V.left) (ha : Etale a)
    (hv : Points.mapOfOver a v = y)
    (hN : IsLocallyNoetherian (residueFiberOver f a v)) :
    existsEtale f y :=
  sorry

/-- `existsEtale f y` supplies an étale scheme chart through `y` whose residue-field
fibre is locally Noetherian. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {y : Points Y}
    (h : existsEtale f y) :
    ∃ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left),
      Etale a ∧ Points.mapOfOver a v = y ∧
        IsLocallyNoetherian (residueFiberOver f a v) :=
  sorry

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
  sorry

namespace forallEtale

/-- The universal étale-chart condition witnesses `forallEtale f y`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {y : Points Y}
    (h : ∀ (V : Over S) (a : ofOver V ⟶ Y) (v : V.left),
      Etale a → Points.mapOfOver a v = y →
        IsLocallyNoetherian (residueFiberOver f a v)) :
    forallEtale f y :=
  sorry

/-- If `forallEtale f y`, then every étale scheme chart through `y` has locally
Noetherian residue-field fibre. -/
theorem apply {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {y : Points Y}
    (h : forallEtale f y) {V : Over S} (a : ofOver V ⟶ Y) (v : V.left)
    (ha : Etale a) (hv : Points.mapOfOver a v = y) :
    IsLocallyNoetherian (residueFiberOver f a v) :=
  sorry

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
  sorry

namespace existsField

/-- A field-valued representative of `y` with locally Noetherian fibre witnesses
`existsField f y`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {y : Points Y}
    (p : FieldValuedPoint Y) (hp : Points.mk p = y)
    (hN : IsLocallyNoetherian (fieldFiber f p)) : existsField f y :=
  sorry

/-- `existsField f y` supplies a field-valued representative of `y` with locally
Noetherian fibre. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {y : Points Y}
    (h : existsField f y) :
    ∃ p : FieldValuedPoint Y, Points.mk p = y ∧ IsLocallyNoetherian (fieldFiber f p) :=
  sorry

/-- A morphism `Spec(k) ⟶ Y` over `S` representing `y` with locally Noetherian
fibre witnesses `existsField f y`. -/
theorem of_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {y : Points Y}
    (k : Type u) [Field k] (σ : Spec (.of k) ⟶ S) (g : ofOver (Over.mk σ) ⟶ Y)
    (hp : Points.mk (FieldValuedPoint.of k σ g) = y)
    (hN : IsLocallyNoetherian (fieldFiber f (FieldValuedPoint.of k σ g))) :
    existsField f y :=
  sorry

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
  sorry

end LocallyNoetherianFiber

end AlgebraicGeometry.AlgebraicSpace
