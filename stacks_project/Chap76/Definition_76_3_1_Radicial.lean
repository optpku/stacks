/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_12_5_Reduced

/-!
# Radicial morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme is radicial when every field-valued
fibre, after reduction, is empty or the spectrum of a purely inseparable extension
of the source field. This is strictly stronger than universal injectivity.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The algebraic space over `S` represented by `Spec(L)`, structured over `S` by
`Spec.map (algebraMap K L) ≫ σ`. -/
abbrev specFieldExtension {S : Scheme.{u}} {K : Type u} [Field K]
    (σ : Spec (.of K) ⟶ S) (L : Type u) [Field L] [Algebra K L] :
    AlgebraicSpace S :=
  ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ σ))

/-- `specFieldExtension σ L` is `ofOver` of `Spec(L)` with structure morphism
`Spec.map (algebraMap K L) ≫ σ`. -/
theorem specFieldExtension_eq {S : Scheme.{u}} {K : Type u} [Field K]
    (σ : Spec (.of K) ⟶ S) (L : Type u) [Field L] [Algebra K L] :
    specFieldExtension σ L =
      ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ σ)) :=
  sorry

/-- The morphism `Spec(L) ⟶ Spec(K)` of algebraic spaces over `S` induced by
`algebraMap K L`. -/
def specFieldExtensionHom {S : Scheme.{u}} {K : Type u} [Field K]
    (σ : Spec (.of K) ⟶ S) (L : Type u) [Field L] [Algebra K L] :
    specFieldExtension σ L ⟶ ofOver (Over.mk σ) :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap K L))) rfl

/-- `specFieldExtensionHom σ L` is `ofOverHomMk` of `Spec.map (algebraMap K L)`. -/
theorem specFieldExtensionHom_eq {S : Scheme.{u}} {K : Type u} [Field K]
    (σ : Spec (.of K) ⟶ S) (L : Type u) [Field L] [Algebra K L] :
    specFieldExtensionHom σ L =
      ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap K L))) rfl :=
  sorry

/-- The reduced fibre `(Spec(K) ×_Y X)_red` of `f` at a field-valued point of `Y`. -/
abbrev reducedFiber {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (p : FieldValuedPoint Y) : AlgebraicSpace S :=
  reduction (pullback p.hom f)

/-- `reducedFiber f p` is the reduction of the fibre product `Spec(K) ×_Y X`. -/
theorem reducedFiber_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (p : FieldValuedPoint Y) :
    reducedFiber f p = reduction (pullback p.hom f) :=
  sorry

/-- The structure morphism of the reduced fibre over `Spec(K)`. -/
def reducedFiberHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (p : FieldValuedPoint Y) :
    reducedFiber f p ⟶ ofOver (Over.mk p.structureHom) :=
  reductionι (pullback p.hom f) ≫ pullback.fst p.hom f

/-- `reducedFiberHom f p` is the composite of the reduction inclusion with the
projection to `Spec(K)`. -/
theorem reducedFiberHom_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (p : FieldValuedPoint Y) :
    reducedFiberHom f p =
      reductionι (pullback p.hom f) ≫ pullback.fst p.hom f :=
  sorry

/-- An algebraic space over `Spec(K)` is empty, or isomorphic over `Spec(K)` to
`Spec(L)` for a purely inseparable field extension `L / K`. -/
def isEmptyOrPurelyInseparableOver {S : Scheme.{u}} {K : Type u} [Field K]
    (σ : Spec (.of K) ⟶ S) {X : AlgebraicSpace S}
    (π : X ⟶ ofOver (Over.mk σ)) : Prop :=
  IsEmpty (Points X) ∨
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsPurelyInseparable K L)
      (e : X ≅ specFieldExtension σ L),
      e.hom ≫ specFieldExtensionHom σ L = π

/-- Unfolding of `isEmptyOrPurelyInseparableOver`. -/
theorem isEmptyOrPurelyInseparableOver_iff {S : Scheme.{u}} {K : Type u} [Field K]
    (σ : Spec (.of K) ⟶ S) {X : AlgebraicSpace S}
    (π : X ⟶ ofOver (Over.mk σ)) :
    isEmptyOrPurelyInseparableOver σ π ↔
      IsEmpty (Points X) ∨
        ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsPurelyInseparable K L)
          (e : X ≅ specFieldExtension σ L),
          e.hom ≫ specFieldExtensionHom σ L = π :=
  sorry

namespace isEmptyOrPurelyInseparableOver

/-- The empty algebraic space over `Spec(K)` satisfies
`isEmptyOrPurelyInseparableOver`. -/
theorem of_isEmpty {S : Scheme.{u}} {K : Type u} [Field K]
    (σ : Spec (.of K) ⟶ S) {X : AlgebraicSpace S}
    (π : X ⟶ ofOver (Over.mk σ)) (h : IsEmpty (Points X)) :
    isEmptyOrPurelyInseparableOver σ π :=
  sorry

/-- An algebraic space isomorphic over `Spec(K)` to `Spec(L)` for a purely
inseparable extension `L / K` satisfies `isEmptyOrPurelyInseparableOver`. -/
theorem of_specField {S : Scheme.{u}} {K : Type u} [Field K]
    (σ : Spec (.of K) ⟶ S) {X : AlgebraicSpace S}
    (π : X ⟶ ofOver (Over.mk σ)) (L : Type u) [Field L] [Algebra K L]
    [IsPurelyInseparable K L] (e : X ≅ specFieldExtension σ L)
    (h : e.hom ≫ specFieldExtensionHom σ L = π) :
    isEmptyOrPurelyInseparableOver σ π :=
  sorry

end isEmptyOrPurelyInseparableOver

/-- A morphism of algebraic spaces is radicial if every reduced field-valued fibre
is empty or the spectrum of a purely inseparable extension of the source field. -/
@[mk_iff]
class Radicial {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- Every reduced fibre `Spec(K) ×_Y X` is empty or `Spec(L)` for a purely
  inseparable extension `L / K`. -/
  reducedPullback :
    ∀ p : FieldValuedPoint Y,
      isEmptyOrPurelyInseparableOver p.structureHom (reducedFiberHom f p)

namespace Radicial

/-- The identity morphism of an algebraic space is radicial. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Radicial (𝟙 X) :=
  sorry

/-- A radicial morphism has empty-or-purely-inseparable reduced field-valued fibres. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Radicial f] (p : FieldValuedPoint Y) :
    isEmptyOrPurelyInseparableOver p.structureHom (reducedFiberHom f p) :=
  sorry

/-- A morphism is radicial as soon as every reduced field-valued fibre is empty or
the spectrum of a purely inseparable extension. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : ∀ p : FieldValuedPoint Y,
      isEmptyOrPurelyInseparableOver p.structureHom (reducedFiberHom f p)) :
    Radicial f :=
  sorry

end Radicial

/-- A morphism of algebraic spaces is radicial if and only if for every field `K`
and every morphism `Spec(K) ⟶ Y`, the reduced fibre is empty or `Spec(L)` for a
purely inseparable extension `L / K`. -/
theorem radicial_iff_forall_specField {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    Radicial f ↔
      ∀ (K : Type u) [Field K] (σ : Spec (.of K) ⟶ S)
        (g : ofOver (Over.mk σ) ⟶ Y),
        isEmptyOrPurelyInseparableOver σ
          (reductionι (pullback g f) ≫ pullback.fst g f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
