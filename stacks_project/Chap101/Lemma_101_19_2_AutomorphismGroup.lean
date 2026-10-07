module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap101.Lemma_101_6_6_Isom

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
  sorry

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
  sorry

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
  sorry

/-- The automorphism group algebraic space of a field-valued point has a
morphism property `P` of algebraic spaces over `S`. -/
def Has {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : MorphismProperty (AlgebraicSpace S)) (p : FieldValuedPoint X) :
    Prop :=
  Groupoids.Hom.has P (structureHom p)

/-- `Has P p` means that the structure morphism of the automorphism group
object has `P` in the sense of `Groupoids.Hom.has`. -/
theorem Has_iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : MorphismProperty (AlgebraicSpace S)) (p : FieldValuedPoint X) :
    Has P p ↔ Groupoids.Hom.has P (structureHom p) :=
  sorry

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
  sorry

/-- Finite morphisms of algebraic spaces are invariant under ground field
extensions. -/
instance isFinite_isInvariantUnderGroundFieldExtension {S : Scheme.{u}} :
    IsInvariantUnderGroundFieldExtension (@AlgebraicSpace.IsFinite S) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
