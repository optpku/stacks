module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Isom.Comparison

/-!
# Automorphism group algebraic spaces of field-valued points

For a field-valued point `p : Spec(k) ⟶ X` of a category fibred in groupoids
over `S`, the automorphism group object `G` is the Isom 2-fibre product
`Isom_X(p, p)`, with structure morphism to `Spec(k)`. A morphism property of
algebraic spaces over `S` is invariant under ground field extensions when it is
unchanged by base change along `FieldExtension.specMap`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open FiberedCategoryOver.Groupoids
open CategoryTheory.Limits
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace FieldValuedPoint

/-- The morphism `Spec(k) ⟶ X` of a field-valued point, as a 1-morphism from
the groupoid fibration of `AlgebraicSpace.ofOver p.overObj`. -/
def toHom {S : Scheme.{u}} {X : GroupoidsOver S} (p : FieldValuedPoint X) :
    (AlgebraicSpace.ofOver p.overObj).toGroupoids ⟶ X :=
  (AlgebraicSpace.ofOverSliceEquiv p.overObj).hom ≫ p.hom

/-- `toHom p` is the slice morphism of `p` transported along
`AlgebraicSpace.ofOverSliceEquiv`. -/
theorem toHom_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    (p : FieldValuedPoint X) :
    p.toHom = (AlgebraicSpace.ofOverSliceEquiv p.overObj).hom ≫ p.hom :=
  rfl

end FieldValuedPoint

/-- The automorphism group object of a field-valued point, as the Isom 2-fibre
product `Isom_X(p, p)`. -/
def automorphismGroup {S : Scheme.{u}} {X : GroupoidsOver S}
    (p : FieldValuedPoint X) : GroupoidsOver S :=
  isomApex p.toHom p.toHom

/-- The automorphism group object of `p` is `isomApex p.toHom p.toHom`. -/
theorem automorphismGroup_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    (p : FieldValuedPoint X) :
    automorphismGroup p = isomApex p.toHom p.toHom :=
  rfl

namespace automorphismGroup

/-- The structure morphism `G ⟶ Spec(k)` of the automorphism group object of a
field-valued point. -/
def structureHom {S : Scheme.{u}} {X : GroupoidsOver S}
    (p : FieldValuedPoint X) :
    automorphismGroup p ⟶ (AlgebraicSpace.ofOver p.overObj).toGroupoids :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u}
    (diagonal.{u + 1, u, u + 1} (AlgebraicSpace.ofOver p.overObj).toGroupoids)
    (toSelfProduct p.toHom p.toHom)

/-- `structureHom p` is the first projection of the Isom 2-fibre product. -/
theorem structureHom_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    (p : FieldValuedPoint X) :
    structureHom p =
      TwoFibreProduct.fst.{u + 1, u, u + 1, u}
        (diagonal.{u + 1, u, u + 1}
          (AlgebraicSpace.ofOver p.overObj).toGroupoids)
        (toSelfProduct p.toHom p.toHom) :=
  rfl

/-- The automorphism group of a field-valued point has `P` over its source
field if every algebraic-space representation of its structure morphism over
that field has `P`. -/
def Has {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : MorphismProperty (AlgebraicSpace S)) (p : FieldValuedPoint X) :
    Prop :=
  ∀ (G : AlgebraicSpace S) (g : G ⟶ AlgebraicSpace.ofOver p.overObj),
    RepresentsBaseChange (structureHom p)
      (AlgebraicSpace.ofOverSliceEquiv p.overObj).inv G g → P g

/-- The automorphism group has `P` over the source field exactly when `P`
holds for every representation of its structure morphism over that field. -/
theorem Has_iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : MorphismProperty (AlgebraicSpace S)) (p : FieldValuedPoint X) :
    Has P p ↔
      ∀ (G : AlgebraicSpace S) (g : G ⟶ AlgebraicSpace.ofOver p.overObj),
        RepresentsBaseChange (structureHom p)
          (AlgebraicSpace.ofOverSliceEquiv p.overObj).inv G g → P g :=
  by rfl

/-- The comparison `G_p ⟶ G_{p ≫ f}` of automorphism group algebraic spaces
induced by a morphism of algebraic stacks is an isomorphism. -/
def IsIsoMap {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) (p : FieldValuedPoint X) : Prop :=
  Groupoids.Hom.has (MorphismProperty.isomorphisms (AlgebraicSpace S))
    (isomComparison f p.toHom p.toHom)

/-- `IsIsoMap f p` means that the Isom comparison of automorphism groups along
`f` at `p` has the isomorphisms morphism property of algebraic spaces. -/
theorem IsIsoMap_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (p : FieldValuedPoint X) :
    IsIsoMap f p ↔
      Groupoids.Hom.has (MorphismProperty.isomorphisms (AlgebraicSpace S))
        (isomComparison f p.toHom p.toHom) :=
  Iff.rfl

end automorphismGroup

/-- A morphism property of algebraic spaces over `S` is invariant under ground
field extensions if it is unchanged by base change along
`Spec(K) ⟶ Spec(k)`. -/
class IsInvariantUnderGroundFieldExtension {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) : Prop where
  /-- `P` holds for a morphism to `Spec(k)` if and only if it holds after base
  change along `FieldExtension.specMap k K`. -/
  iff_groundFieldExtension {k K : Type u} [Field k] [Field K] [Algebra k K]
      {σk : Spec (.of k) ⟶ S} {σK : Spec (.of K) ⟶ S}
      (hσ : FieldExtension.specMap k K ≫ σk = σK)
      {X XK : AlgebraicSpace S}
      {f : X ⟶ AlgebraicSpace.ofOver (Over.mk σk)}
      {g : XK ⟶ AlgebraicSpace.ofOver (Over.mk σK)} {h : XK ⟶ X}
      (sq : IsPullback g h
        (AlgebraicSpace.ofOverHomMk (FieldExtension.specMap k K) hσ) f) :
      P f ↔ P g

/-- Invariance under ground field extensions means `P f ↔ P g` on every
base-change square along `FieldExtension.specMap`. -/
theorem IsInvariantUnderGroundFieldExtension.iff {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [IsInvariantUnderGroundFieldExtension P] {k K : Type u} [Field k]
    [Field K] [Algebra k K] {σk : Spec (.of k) ⟶ S}
    {σK : Spec (.of K) ⟶ S} (hσ : FieldExtension.specMap k K ≫ σk = σK)
    {X XK : AlgebraicSpace S} {f : X ⟶ AlgebraicSpace.ofOver (Over.mk σk)}
    {g : XK ⟶ AlgebraicSpace.ofOver (Over.mk σK)} {h : XK ⟶ X}
    (sq : IsPullback g h
      (AlgebraicSpace.ofOverHomMk (FieldExtension.specMap k K) hσ) f) :
    P f ↔ P g :=
  IsInvariantUnderGroundFieldExtension.iff_groundFieldExtension hσ sq

/-- Finite morphisms of algebraic spaces are invariant under ground field
extensions. -/
instance isFinite_isInvariantUnderGroundFieldExtension {S : Scheme.{u}} :
    IsInvariantUnderGroundFieldExtension (@AlgebraicSpace.IsFinite S) :=
  sorry

/-- For a property invariant under ground field extensions, the automorphism
group has that property for some field-valued representative of a point of an
algebraic stack if and only if it has it for every representative. -/
@[stacks 0DTT]
theorem automorphismGroup_has_exists_iff_forall {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] (x : |X|)
    (P : MorphismProperty (AlgebraicSpace S))
    [IsInvariantUnderGroundFieldExtension P] :
    (∃ p : FieldValuedPoint X, Points.mk p = x ∧ automorphismGroup.Has P p) ↔
      (∀ p : FieldValuedPoint X, Points.mk p = x →
        automorphismGroup.Has P p) :=
  sorry
/-- The automorphism-group comparison induced by a morphism of algebraic
stacks is an isomorphism for some field-valued representative of a point if
and only if it is an isomorphism for every representative. -/
@[stacks 0DTV]
theorem automorphismGroup_isIsoMap_exists_iff_forall {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (x : |X|) :
    (∃ p : FieldValuedPoint X, Points.mk p = x ∧ automorphismGroup.IsIsoMap f p) ↔
      (∀ p : FieldValuedPoint X, Points.mk p = x →
        automorphismGroup.IsIsoMap f p) :=
  sorry

/-- Smooth morphisms of algebraic spaces are invariant under ground field
extensions. -/
instance smooth_isInvariantUnderGroundFieldExtension {S : Scheme.{u}} :
    IsInvariantUnderGroundFieldExtension (@AlgebraicSpace.Smooth S) :=
  sorry

/-- Proper morphisms of algebraic spaces are invariant under ground field
extensions. -/
instance proper_isInvariantUnderGroundFieldExtension {S : Scheme.{u}} :
    IsInvariantUnderGroundFieldExtension (@AlgebraicSpace.Proper S) :=
  sorry

namespace automorphismGroup

/-- The automorphism group of an algebraic stack at a point has a morphism
property `P` of algebraic spaces over fields, invariant under ground field
extensions, when every field-valued representative of the point has `P`. -/
def HasAt {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : MorphismProperty (AlgebraicSpace S))
    [IsInvariantUnderGroundFieldExtension P] (x : |X|) : Prop :=
  ∀ p : FieldValuedPoint X, Points.mk p = x → Has P p

/-- The automorphism group at a point has `P` if and only if some field-valued
representative has `P`. -/
theorem HasAt_iff_exists {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (P : MorphismProperty (AlgebraicSpace S))
    [IsInvariantUnderGroundFieldExtension P] (x : |X|) :
    HasAt P x ↔ ∃ p : FieldValuedPoint X, Points.mk p = x ∧ Has P p :=
  sorry

namespace HasAt

/-- If the automorphism group at `x` has `P`, then the automorphism group of
every field-valued representative of `x` has `P`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : MorphismProperty (AlgebraicSpace S))
    [IsInvariantUnderGroundFieldExtension P] {x : |X|} :
    HasAt P x → ∀ p : FieldValuedPoint X, Points.mk p = x → Has P p :=
  sorry

/-- If the automorphism group of a field-valued representative of `x` has `P`,
then the automorphism group at `x` has `P`. -/
theorem of_fieldValuedPoint {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (P : MorphismProperty (AlgebraicSpace S))
    [IsInvariantUnderGroundFieldExtension P] {x : |X|} {p : FieldValuedPoint X} :
    Points.mk p = x → Has P p → HasAt P x :=
  sorry

end HasAt

/-- The automorphism group of an algebraic stack at a point is finite. -/
def IsFinite {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (x : |X|) : Prop :=
  HasAt (@AlgebraicSpace.IsFinite S) x

/-- The automorphism group at `x` is finite if and only if the structure
morphism of the automorphism group of every field-valued representative is
finite. -/
theorem IsFinite_iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (x : |X|) :
    IsFinite x ↔
      ∀ p : FieldValuedPoint X, Points.mk p = x →
        Has (@AlgebraicSpace.IsFinite S) p :=
  sorry

/-- The automorphism group of an algebraic stack at a point is smooth. -/
def Smooth {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (x : |X|) : Prop :=
  HasAt (@AlgebraicSpace.Smooth S) x

/-- The automorphism group at `x` is smooth if and only if the structure
morphism of the automorphism group of every field-valued representative is
smooth. -/
theorem Smooth_iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (x : |X|) :
    Smooth x ↔
      ∀ p : FieldValuedPoint X, Points.mk p = x →
        Has (@AlgebraicSpace.Smooth S) p :=
  sorry

/-- The automorphism group of an algebraic stack at a point is proper. -/
def Proper {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (x : |X|) : Prop :=
  HasAt (@AlgebraicSpace.Proper S) x

/-- The automorphism group at `x` is proper if and only if the structure
morphism of the automorphism group of every field-valued representative is
proper. -/
theorem Proper_iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (x : |X|) :
    Proper x ↔
      ∀ p : FieldValuedPoint X, Points.mk p = x →
        Has (@AlgebraicSpace.Proper S) p :=
  sorry

end automorphismGroup

namespace automorphismGroup

/-- A morphism induces an isomorphism between automorphism groups at a point
and its image when its canonical comparison is an isomorphism for every
field-valued representative of the point. -/
def IsIsoAt {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) (x : |X|) : Prop :=
  ∀ p : FieldValuedPoint X, Points.mk p = x → IsIsoMap f p

/-- `IsIsoAt f x` means that the automorphism-group comparison along `f` is an
isomorphism at every field-valued representative of `x`. -/
theorem IsIsoAt_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : |X|) :
    IsIsoAt f x ↔ ∀ p : FieldValuedPoint X, Points.mk p = x → IsIsoMap f p :=
  Iff.rfl

/-- `IsIsoAt f x` if and only if some field-valued representative of `x` has
an isomorphic automorphism-group comparison along `f`. -/
theorem IsIsoAt_iff_exists {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : |X|) :
    IsIsoAt f x ↔ ∃ p : FieldValuedPoint X, Points.mk p = x ∧ IsIsoMap f p :=
  (automorphismGroup_isIsoMap_exists_iff_forall f x).symm

namespace IsIsoAt

/-- If `f` induces an isomorphism of automorphism groups at `x`, then the
comparison along `f` is an isomorphism at every field-valued representative
of `x`. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] {f : X ⟶ Y} {x : |X|} :
    IsIsoAt f x → ∀ p : FieldValuedPoint X, Points.mk p = x → IsIsoMap f p :=
  fun h p hp => h p hp

/-- If the automorphism-group comparison along `f` is an isomorphism at one
field-valued representative of `x`, then `f` induces an isomorphism of
automorphism groups at `x`. -/
theorem of_fieldValuedPoint {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} {x : |X|}
    {p : FieldValuedPoint X} :
    Points.mk p = x → IsIsoMap f p → IsIsoAt f x :=
  fun hp h => (IsIsoAt_iff_exists f x).mpr ⟨p, hp, h⟩

end IsIsoAt

end automorphismGroup

/-- A morphism is stabilizer preserving at a point when it induces an
isomorphism between automorphism groups at that point and its image. -/
abbrev IsStabilizerPreservingAt {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : |X|) : Prop :=
  automorphismGroup.IsIsoAt f x

/-- A morphism is fixed-point reflecting at a point when it induces an
isomorphism between automorphism groups at that point and its image. -/
abbrev IsFixedPointReflectingAt {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : |X|) : Prop :=
  automorphismGroup.IsIsoAt f x

end AlgebraicGeometry.AlgebraicStack
