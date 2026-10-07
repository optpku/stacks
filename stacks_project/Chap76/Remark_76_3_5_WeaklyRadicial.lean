module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap76.Definition_76_3_1_Radicial

/-!
# Weakly radicial morphisms of algebraic spaces

A morphism of algebraic spaces is weakly radicial when every field-valued fibre
has singleton points space and admits a monomorphism from the spectrum of a
purely inseparable extension of the source field. This is strictly weaker than
being radicial, which requires the reduced fibre to be empty or isomorphic to
such a spectrum.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space over `Spec(K)` has singleton points space and admits a
monomorphism from `Spec(L)` over `Spec(K)` for a purely inseparable field
extension `L / K`. -/
def isWeaklyRadicialOver {S : Scheme.{u}} {K : Type u} [Field K]
    (σ : Spec (.of K) ⟶ S) {X : AlgebraicSpace S}
    (π : X ⟶ ofOver (Over.mk σ)) : Prop :=
  Nonempty (Points X) ∧ Subsingleton (Points X) ∧
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsPurelyInseparable K L)
      (ι : specFieldExtension σ L ⟶ X),
      Mono ι ∧ ι ≫ π = specFieldExtensionHom σ L

/-- Unfolding of `isWeaklyRadicialOver`. -/
theorem isWeaklyRadicialOver_iff {S : Scheme.{u}} {K : Type u} [Field K]
    (σ : Spec (.of K) ⟶ S) {X : AlgebraicSpace S}
    (π : X ⟶ ofOver (Over.mk σ)) :
    isWeaklyRadicialOver σ π ↔
      Nonempty (Points X) ∧ Subsingleton (Points X) ∧
        ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsPurelyInseparable K L)
          (ι : specFieldExtension σ L ⟶ X),
          Mono ι ∧ ι ≫ π = specFieldExtensionHom σ L :=
  sorry

namespace isWeaklyRadicialOver

/-- An algebraic space over `Spec(K)` with singleton points and a monomorphism
from `Spec(L)` over `Spec(K)` for a purely inseparable extension `L / K`
satisfies `isWeaklyRadicialOver`. -/
theorem of {S : Scheme.{u}} {K : Type u} [Field K] (σ : Spec (.of K) ⟶ S)
    {X : AlgebraicSpace S} (π : X ⟶ ofOver (Over.mk σ))
    (h_points : Nonempty (Points X) ∧ Subsingleton (Points X)) (L : Type u)
    [Field L] [Algebra K L] [IsPurelyInseparable K L]
    (ι : specFieldExtension σ L ⟶ X) [Mono ι]
    (h_triangle : ι ≫ π = specFieldExtensionHom σ L) :
    isWeaklyRadicialOver σ π :=
  sorry

/-- `isWeaklyRadicialOver` implies singleton points and a monomorphism from
`Spec(L)` over `Spec(K)` for a purely inseparable extension `L / K`. -/
theorem spec {S : Scheme.{u}} {K : Type u} [Field K] (σ : Spec (.of K) ⟶ S)
    {X : AlgebraicSpace S} (π : X ⟶ ofOver (Over.mk σ))
    (h : isWeaklyRadicialOver σ π) :
    Nonempty (Points X) ∧ Subsingleton (Points X) ∧
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsPurelyInseparable K L)
        (ι : specFieldExtension σ L ⟶ X),
        Mono ι ∧ ι ≫ π = specFieldExtensionHom σ L :=
  sorry

/-- A weakly radicial fibre over `Spec(K)` has singleton points space. -/
theorem unique_points {S : Scheme.{u}} {K : Type u} [Field K]
    (σ : Spec (.of K) ⟶ S) {X : AlgebraicSpace S}
    (π : X ⟶ ofOver (Over.mk σ)) (h : isWeaklyRadicialOver σ π) :
    Nonempty (Points X) ∧ Subsingleton (Points X) :=
  sorry

/-- A weakly radicial fibre over `Spec(K)` admits a monomorphism from `Spec(L)`
over `Spec(K)` for a purely inseparable extension `L / K`. -/
theorem exists_mono {S : Scheme.{u}} {K : Type u} [Field K]
    (σ : Spec (.of K) ⟶ S) {X : AlgebraicSpace S}
    (π : X ⟶ ofOver (Over.mk σ)) (h : isWeaklyRadicialOver σ π) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsPurelyInseparable K L)
      (ι : specFieldExtension σ L ⟶ X),
      Mono ι ∧ ι ≫ π = specFieldExtensionHom σ L :=
  sorry

end isWeaklyRadicialOver

/-- A morphism of algebraic spaces is weakly radicial if every field-valued fibre
has singleton points space and admits a monomorphism from the spectrum of a
purely inseparable extension of the source field. -/
@[mk_iff]
class WeaklyRadicial {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop where
  /-- Every fibre `Spec(K) ×_Y X` is weakly radicial over `Spec(K)`. -/
  fieldValuedPullback :
    ∀ p : FieldValuedPoint Y,
      isWeaklyRadicialOver p.structureHom (pullback.fst p.hom f)

namespace WeaklyRadicial

/-- The identity morphism of an algebraic space is weakly radicial. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : WeaklyRadicial (𝟙 X) :=
  sorry

/-- A weakly radicial morphism has weakly radicial field-valued fibres. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [WeaklyRadicial f] (p : FieldValuedPoint Y) :
    isWeaklyRadicialOver p.structureHom (pullback.fst p.hom f) :=
  sorry

/-- A morphism is weakly radicial as soon as every field-valued fibre is weakly
radicial over `Spec(K)`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : ∀ p : FieldValuedPoint Y,
      isWeaklyRadicialOver p.structureHom (pullback.fst p.hom f)) :
    WeaklyRadicial f :=
  sorry

/-- A weakly radicial morphism has singleton field-valued fibres. -/
theorem unique_points {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [WeaklyRadicial f] (p : FieldValuedPoint Y) :
    Nonempty (Points (pullback p.hom f)) ∧
      Subsingleton (Points (pullback p.hom f)) :=
  sorry

/-- A weakly radicial morphism has, on every field-valued fibre, a monomorphism
from `Spec(L)` over `Spec(K)` for a purely inseparable extension `L / K`. -/
theorem exists_mono {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [WeaklyRadicial f] (p : FieldValuedPoint Y) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra p.K L)
      (_ : IsPurelyInseparable p.K L)
      (ι : specFieldExtension p.structureHom L ⟶ pullback p.hom f),
      Mono ι ∧
        ι ≫ pullback.fst p.hom f = specFieldExtensionHom p.structureHom L :=
  sorry

/-- A weakly radicial morphism is surjective, since every field-valued fibre has
singleton points space. -/
instance surjective {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [WeaklyRadicial f] : Surjective f :=
  sorry

end WeaklyRadicial

/-- A morphism of algebraic spaces is weakly radicial if and only if for every
field `K` and every morphism `Spec(K) ⟶ Y`, the fibre `Spec(K) ×_Y X` is weakly
radicial over `Spec(K)`. -/
theorem weaklyRadicial_iff_forall_specField {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    WeaklyRadicial f ↔
      ∀ (K : Type u) [Field K] (σ : Spec (.of K) ⟶ S)
        (g : ofOver (Over.mk σ) ⟶ Y),
        isWeaklyRadicialOver σ (pullback.fst g f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
