/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.TensorProduct.Maps
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_2_Pullback

/-!
# Affine fibre products of schemes over an algebraic space

The representing scheme of a fibre product `U ×_X V` of morphisms from schemes into an
algebraic space, together with its comparison morphism to the absolute product `U × V` and the
induced tensor map on global sections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The representing scheme of the fibre product of two morphisms from schemes over `S` into an
algebraic space `X`. -/
def schemePullback {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) : Over S :=
  pullbackOverAtlas (𝟙 X.functorOfPoints) (𝟙 X.functorOfPoints) X.representableDiagonal f g

/-- `schemePullback f g` is the atlas fibre product of the Yoneda sections `f` and `g`. -/
theorem schemePullback_eq {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    schemePullback f g =
      pullbackOverAtlas (𝟙 X.functorOfPoints) (𝟙 X.functorOfPoints) X.representableDiagonal f g :=
  sorry

namespace schemePullback

/-- The first projection `U ×_X V ⟶ U` of the representing fibre product. -/
def fst {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) : schemePullback f g ⟶ U :=
  yoneda.preimage
    (pullbackOverAtlasFst (𝟙 X.functorOfPoints) (𝟙 X.functorOfPoints) X.representableDiagonal f g)

/-- The second projection `U ×_X V ⟶ V` of the representing fibre product. -/
def snd {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) : schemePullback f g ⟶ V :=
  pullbackOverAtlasSnd (𝟙 X.functorOfPoints) (𝟙 X.functorOfPoints) X.representableDiagonal f g

/-- The comparison morphism `U ×_X V ⟶ U × V` into the absolute product of underlying schemes. -/
def toProd {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    (schemePullback f g).left ⟶ U.left ⨯ V.left :=
  prod.lift (fst f g).left (snd f g).left

/-- `toProd f g` is the product lift of the underlying scheme morphisms of the two projections. -/
theorem toProd_eq {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    toProd f g = prod.lift (fst f g).left (snd f g).left :=
  sorry

/-- The induced map `Γ(U, ⊤) ⊗[ℤ] Γ(V, ⊤) ⟶ Γ(U ×_X V, ⊤)` obtained by lifting the two
projection maps on global sections. -/
def tensorHom {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    CommRingCat.of (Γ(U.left, ⊤) ⊗[ℤ] Γ(V.left, ⊤)) ⟶ Γ((schemePullback f g).left, ⊤) :=
  CommRingCat.ofHom
    (Algebra.TensorProduct.lift
        (RingHom.toIntAlgHom (fst f g).left.appTop.hom)
        (RingHom.toIntAlgHom (snd f g).left.appTop.hom)
        fun _ _ ↦ Commute.all _ _).toRingHom

/-- `tensorHom f g` is the tensor-product lift of the two projection maps on global sections. -/
theorem tensorHom_eq {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    tensorHom f g =
      CommRingCat.ofHom
        (Algebra.TensorProduct.lift
            (RingHom.toIntAlgHom (fst f g).left.appTop.hom)
            (RingHom.toIntAlgHom (snd f g).left.appTop.hom)
            fun _ _ ↦ Commute.all _ _).toRingHom :=
  sorry

/-- The Yoneda square of the two projections exhibits `schemePullback f g` as the fibre product
of `f` and `g`. -/
theorem isPullback {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    IsPullback (yoneda.map (fst f g)) (yoneda.map (snd f g)) f g :=
  sorry

end schemePullback

/-- Fibre products of morphisms from affine schemes to `X` are affine, and the induced
`ℤ`-tensor map on global sections is surjective. -/
def forallAffinePullbackAffineSurjective {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop :=
  ∀ (U V : Over S) [IsAffine U.left] [IsAffine V.left]
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X),
    IsAffine (schemePullback f g).left ∧ Function.Surjective (schemePullback.tensorHom f g).hom

/-- `forallAffinePullbackAffineSurjective X` means that affine tests `U ⟶ X` and `V ⟶ X` have
affine fibre product with surjective tensor map on global sections. -/
theorem forallAffinePullbackAffineSurjective_iff {S : Scheme.{u}} (X : AlgebraicSpace S) :
    forallAffinePullbackAffineSurjective X ↔
      ∀ (U V : Over S) [IsAffine U.left] [IsAffine V.left]
        (f : ofOver U ⟶ X) (g : ofOver V ⟶ X),
        IsAffine (schemePullback f g).left ∧
          Function.Surjective (schemePullback.tensorHom f g).hom :=
  sorry

namespace forallAffinePullbackAffineSurjective

/-- The universal affine-scheme pullback condition witnesses
`forallAffinePullbackAffineSurjective X`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ (U V : Over S) [IsAffine U.left] [IsAffine V.left]
      (f : ofOver U ⟶ X) (g : ofOver V ⟶ X),
      IsAffine (schemePullback f g).left ∧
        Function.Surjective (schemePullback.tensorHom f g).hom) :
    forallAffinePullbackAffineSurjective X :=
  sorry

/-- If `forallAffinePullbackAffineSurjective X`, then the fibre product of morphisms from affine
schemes to `X` is affine with surjective tensor map on global sections. -/
theorem apply {S : Scheme.{u}} {X : AlgebraicSpace S} (h : forallAffinePullbackAffineSurjective X)
    {U V : Over S} [IsAffine U.left] [IsAffine V.left]
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    IsAffine (schemePullback f g).left ∧ Function.Surjective (schemePullback.tensorHom f g).hom :=
  sorry

end forallAffinePullbackAffineSurjective

/-- Fibre products of morphisms from affine schemes to `X` induce a closed immersion into the
absolute product of the underlying schemes. -/
def forallAffinePullbackClosedImmersion {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop :=
  ∀ (U V : Over S) [IsAffine U.left] [IsAffine V.left]
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X),
    IsClosedImmersion (schemePullback.toProd f g)

/-- `forallAffinePullbackClosedImmersion X` means that affine tests `U ⟶ X` and `V ⟶ X` have
comparison morphism `U ×_X V ⟶ U × V` a closed immersion. -/
theorem forallAffinePullbackClosedImmersion_iff {S : Scheme.{u}} (X : AlgebraicSpace S) :
    forallAffinePullbackClosedImmersion X ↔
      ∀ (U V : Over S) [IsAffine U.left] [IsAffine V.left]
        (f : ofOver U ⟶ X) (g : ofOver V ⟶ X),
        IsClosedImmersion (schemePullback.toProd f g) :=
  sorry

namespace forallAffinePullbackClosedImmersion

/-- The universal closed-immersion condition on affine tests witnesses
`forallAffinePullbackClosedImmersion X`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ (U V : Over S) [IsAffine U.left] [IsAffine V.left]
      (f : ofOver U ⟶ X) (g : ofOver V ⟶ X),
      IsClosedImmersion (schemePullback.toProd f g)) :
    forallAffinePullbackClosedImmersion X :=
  sorry

/-- If `forallAffinePullbackClosedImmersion X`, then the comparison of an affine test fibre
product to the absolute product is a closed immersion. -/
theorem apply {S : Scheme.{u}} {X : AlgebraicSpace S} (h : forallAffinePullbackClosedImmersion X)
    {U V : Over S} [IsAffine U.left] [IsAffine V.left]
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    IsClosedImmersion (schemePullback.toProd f g) :=
  sorry

end forallAffinePullbackClosedImmersion

/-- On affine tests, the comparison `U ×_X V ⟶ U × V` is a closed immersion if and only if the
fibre product is affine and the tensor map on global sections is surjective. -/
theorem forallAffinePullbackClosedImmersion_iff_affine_surjective
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    [IsAffine U.left] [IsAffine V.left] (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    IsClosedImmersion (schemePullback.toProd f g) ↔
      IsAffine (schemePullback f g).left ∧
        Function.Surjective (schemePullback.tensorHom f g).hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
