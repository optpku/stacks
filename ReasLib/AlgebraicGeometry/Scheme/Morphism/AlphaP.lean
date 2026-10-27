/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.RingTheory.AdjoinRoot
public import ReasLib.AlgebraicGeometry.Scheme.Characteristic.Prime
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The affine `α_p`-cover `Spec(R[z] / (z^p - c)) ⟶ Spec(R)` attached to an
element `c` of a commutative ring `R`. -/
noncomputable def adjoinRootAlphaPHom (R : Type u) [CommRing R] (c : R) :
    Spec (.of (AdjoinRoot (Polynomial.X ^ p - Polynomial.C c))) ⟶ Spec (.of R) :=
  Spec.map
    (CommRingCat.ofHom
      (algebraMap R (AdjoinRoot (Polynomial.X ^ p - Polynomial.C c))))

/-- Adjoining a `p`-th root of an element preserves characteristic `p`. -/
instance instCharP_adjoinRootAlphaP (R : Type u) [CommRing R] [CharP R p] (c : R) :
    CharP (AdjoinRoot (Polynomial.X ^ p - Polynomial.C c)) p :=
  sorry

/-- The spectrum of `R[z] / (z^p - c)` is a scheme of characteristic `p`. -/
instance instIsCharP_adjoinRootAlphaP_spec
    (R : Type u) [CommRing R] [CharP R p] (c : R) :
    Scheme.IsCharP (Spec (.of (AdjoinRoot (Polynomial.X ^ p - Polynomial.C c)))) p :=
  inferInstance

/-- A morphism in characteristic `p` is an `α_p`-cover if, locally on the target,
it is the morphism obtained by adjoining a `p`-th root of a function. -/
class IsAlphaPCover {X Y : Scheme.{u}} [Scheme.IsCharP X p] [Scheme.IsCharP Y p]
    (f : X ⟶ Y) : Prop where
  /-- An affine open cover on which the morphism has root-adjunction presentations. -/
  exists_adjoinRoot :
    ∃ (𝒰 : Y.AffineOpenCover.{u}), ∀ i : 𝒰.I₀,
      ∃ (R : Type u) (hR : CommRing R) (c : R)
        (eSrc : (Limits.pullback f (𝒰.f i)) ≅
          Spec (.of (AdjoinRoot (Polynomial.X ^ p - Polynomial.C c))))
        (eTgt : 𝒰.openCover.X i ≅ Spec (.of R)),
        eSrc.hom ≫ adjoinRootAlphaPHom p R c =
          𝒰.openCover.pullbackHom f i ≫ eTgt.hom

/-- Root-adjunction morphisms in characteristic `p` are `α_p`-covers. -/
instance instIsAlphaPCover_adjoinRoot (R : Type u) [CommRing R] [CharP R p] (c : R) :
    IsAlphaPCover p (adjoinRootAlphaPHom p R c) := sorry

/-- An `α_p`-cover is characterized by affine root-adjunction presentations
on an affine open cover of its target. -/
theorem isAlphaPCover_iff {X Y : Scheme.{u}} [Scheme.IsCharP X p] [Scheme.IsCharP Y p]
    (f : X ⟶ Y) :
    IsAlphaPCover p f ↔
      ∃ (𝒰 : Y.AffineOpenCover.{u}), ∀ i : 𝒰.I₀,
        ∃ (R : Type u) (hR : CommRing R) (c : R)
          (eSrc : (Limits.pullback f (𝒰.f i)) ≅
            Spec (.of (AdjoinRoot (Polynomial.X ^ p - Polynomial.C c))))
          (eTgt : 𝒰.openCover.X i ≅ Spec (.of R)),
          eSrc.hom ≫ adjoinRootAlphaPHom p R c =
            𝒰.openCover.pullbackHom f i ≫ eTgt.hom := sorry

/-- An `α_p`-cover has characteristic `p` on source and target and admits
local affine root-adjunction presentations. -/
theorem IsAlphaPCover.spec {X Y : Scheme.{u}} [Scheme.IsCharP X p]
    [Scheme.IsCharP Y p] (f : X ⟶ Y) :
    IsAlphaPCover p f ↔
      Scheme.IsCharP X p ∧ Scheme.IsCharP Y p ∧
        ∃ (𝒰 : Y.AffineOpenCover.{u}), ∀ i : 𝒰.I₀,
          ∃ (R : Type u) (hR : CommRing R) (c : R)
            (eSrc : (Limits.pullback f (𝒰.f i)) ≅
              Spec (.of (AdjoinRoot (Polynomial.X ^ p - Polynomial.C c))))
            (eTgt : 𝒰.openCover.X i ≅ Spec (.of R)),
            eSrc.hom ≫ adjoinRootAlphaPHom p R c =
              𝒰.openCover.pullbackHom f i ≫ eTgt.hom := sorry

/-- An `α_p`-cover is finite locally free. -/
theorem isFiniteLocallyFree_ofIsAlphaPCover {X Y : Scheme.{u}}
    [Scheme.IsCharP X p] [Scheme.IsCharP Y p] (f : X ⟶ Y)
    [IsAlphaPCover p f] : IsFiniteLocallyFree f :=
  sorry

/-- An `α_p`-cover has constant rank `p`. -/
instance instIsFiniteLocallyFreeOfRank_ofIsAlphaPCover {X Y : Scheme.{u}}
    [Scheme.IsCharP X p] [Scheme.IsCharP Y p] (f : X ⟶ Y)
    [IsAlphaPCover p f] : IsFiniteLocallyFreeOfRank f p where
  toIsFiniteLocallyFree := isFiniteLocallyFree_ofIsAlphaPCover p f
  pushforward_isFiniteLocallyFreeOfRank := sorry

/-- A finite composition of `α_p`-covers. -/
inductive IsFiniteCompositionOfAlphaPCover :
    {X Y : Scheme.{u}} → (X ⟶ Y) → Prop
  /-- The empty composition is the identity morphism. -/
  | id (X : Scheme.{u}) [Scheme.IsCharP X p] :
      IsFiniteCompositionOfAlphaPCover (𝟙 X)
  /-- A single root-adjunction cover is a finite composition. -/
  | ofAlphaP {X Y : Scheme.{u}} [Scheme.IsCharP X p] [Scheme.IsCharP Y p]
      (f : X ⟶ Y) : IsAlphaPCover p f →
      IsFiniteCompositionOfAlphaPCover f
  /-- Finite compositions are closed under composition. -/
  | comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
      IsFiniteCompositionOfAlphaPCover f →
        IsFiniteCompositionOfAlphaPCover g →
          IsFiniteCompositionOfAlphaPCover (f ≫ g)

/-- A single `α_p`-cover is a finite composition of `α_p`-covers. -/
theorem IsFiniteCompositionOfAlphaPCover.of_isAlphaPCover {X Y : Scheme.{u}}
    [Scheme.IsCharP X p] [Scheme.IsCharP Y p] (f : X ⟶ Y)
    [hf : IsAlphaPCover p f] :
    IsFiniteCompositionOfAlphaPCover p f :=
  sorry

/-- An iterated `α_p`-cover is a morphism which, locally on the target, is a
finite composition of `α_p`-covers. -/
class IsIteratedAlphaPCover {X Y : Scheme.{u}} [Scheme.IsCharP X p]
    [Scheme.IsCharP Y p] (f : X ⟶ Y) : Prop where
  /-- Locally on the target, the morphism is a finite composition of `α_p`-covers. -/
  exists_affineCover :
    ∃ (𝒰 : Y.AffineOpenCover.{u}),
      ∀ i : 𝒰.I₀, IsFiniteCompositionOfAlphaPCover p
        (𝒰.openCover.pullbackHom f i)

/-- A single `α_p`-cover is an iterated `α_p`-cover. -/
instance instIsIteratedAlphaPCover_ofIsAlphaPCover {X Y : Scheme.{u}}
    [Scheme.IsCharP X p] [Scheme.IsCharP Y p] (f : X ⟶ Y)
    [IsAlphaPCover p f] : IsIteratedAlphaPCover p f where
  exists_affineCover := sorry

/-- Characterization of an iterated `α_p`-cover: characteristic `p`
and a target-local finite composition of `α_p`-covers. -/
theorem IsIteratedAlphaPCover.spec {X Y : Scheme.{u}} [Scheme.IsCharP X p]
    [Scheme.IsCharP Y p] (f : X ⟶ Y) :
    IsIteratedAlphaPCover p f ↔
      Scheme.IsCharP X p ∧ Scheme.IsCharP Y p ∧
        ∃ (𝒰 : Y.AffineOpenCover.{u}),
          ∀ i : 𝒰.I₀, IsFiniteCompositionOfAlphaPCover p
            (𝒰.openCover.pullbackHom f i) :=
  sorry

/-- An iterated `α_p`-cover is finite locally free. -/
theorem isFiniteLocallyFree_ofIsIteratedAlphaPCover {X Y : Scheme.{u}}
    [Scheme.IsCharP X p] [Scheme.IsCharP Y p] (f : X ⟶ Y)
    [IsIteratedAlphaPCover p f] : IsFiniteLocallyFree f :=
  sorry

/-- An iterated `α_p`-cover induces a homeomorphism of underlying spaces. -/
theorem IsIteratedAlphaPCover.isHomeomorph {X Y : Scheme.{u}}
    [Scheme.IsCharP X p] [Scheme.IsCharP Y p] (f : X ⟶ Y)
    [IsIteratedAlphaPCover p f] : IsHomeomorph f := sorry

end AlgebraicGeometry
