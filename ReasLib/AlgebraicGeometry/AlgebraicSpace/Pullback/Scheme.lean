/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Scheme fibre products over algebraic spaces

Represented fibre products of schemes over an algebraic space carry projections, a comparison
with the absolute product, and the induced tensor map on global sections.
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
  AlgebraicGeometry.AlgebraicSpace.ReasLibPullback.pullbackOverAtlas
    (𝟙 X.functorOfPoints) (𝟙 X.functorOfPoints) X.representableDiagonal f g

/-- `schemePullback f g` is the atlas fibre product of the Yoneda sections `f` and `g`. -/
theorem schemePullback_eq {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    schemePullback f g =
      AlgebraicGeometry.AlgebraicSpace.ReasLibPullback.pullbackOverAtlas
        (𝟙 X.functorOfPoints) (𝟙 X.functorOfPoints) X.representableDiagonal f g :=
  rfl

namespace schemePullback

/-- The first projection `U ×_X V ⟶ U` of the representing fibre product. -/
def fst {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) : schemePullback f g ⟶ U :=
  yoneda.preimage
    (AlgebraicGeometry.AlgebraicSpace.ReasLibPullback.pullbackOverAtlasFst
      (𝟙 X.functorOfPoints) (𝟙 X.functorOfPoints) X.representableDiagonal f g)

/-- The second projection `U ×_X V ⟶ V` of the representing fibre product. -/
def snd {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) : schemePullback f g ⟶ V :=
  AlgebraicGeometry.AlgebraicSpace.ReasLibPullback.pullbackOverAtlasSnd
    (𝟙 X.functorOfPoints) (𝟙 X.functorOfPoints) X.representableDiagonal f g

/-- The comparison morphism `U ×_X V ⟶ U × V` into the absolute product of underlying schemes. -/
def toProd {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    (schemePullback f g).left ⟶ U.left ⨯ V.left :=
  prod.lift (fst f g).left (snd f g).left

/-- `toProd f g` is the product lift of the underlying scheme morphisms of the two projections. -/
theorem toProd_eq {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    toProd f g = prod.lift (fst f g).left (snd f g).left :=
  rfl

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
  rfl

/-- The Yoneda square of the two projections exhibits `schemePullback f g` as the fibre product
of `f` and `g`. -/
theorem isPullback {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    IsPullback (yoneda.map (fst f g)) (yoneda.map (snd f g)) f g :=
  sorry

/-- On affine tests, the comparison `U ×_X V ⟶ U × V` is a closed immersion if and only if the
fibre product is affine and the tensor map on global sections is surjective. -/
theorem isClosedImmersion_toProd_iff
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    [IsAffine U.left] [IsAffine V.left] (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    IsClosedImmersion (schemePullback.toProd f g) ↔
      IsAffine (schemePullback f g).left ∧
        Function.Surjective (schemePullback.tensorHom f g).hom :=
  sorry

end schemePullback

end AlgebraicGeometry.AlgebraicSpace
