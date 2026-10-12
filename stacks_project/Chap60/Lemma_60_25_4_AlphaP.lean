/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/-- The affine `α_p`-cover is `Spec.map` of the structure map of
`AdjoinRoot (Polynomial.X ^ p - Polynomial.C c)`. -/
theorem adjoinRootAlphaPHom_eq (R : Type u) [CommRing R] (c : R) :
    adjoinRootAlphaPHom p R c =
      Spec.map
        (CommRingCat.ofHom
          (algebraMap R (AdjoinRoot (Polynomial.X ^ p - Polynomial.C c)))) :=
  sorry

/-- Adjoining a `p`-th root of an element preserves characteristic `p`. -/
instance instCharP_adjoinRootAlphaP (R : Type u) [CommRing R] [CharP R p] (c : R) :
    CharP (AdjoinRoot (Polynomial.X ^ p - Polynomial.C c)) p :=
  sorry

/-- The spectrum of `R[z] / (z^p - c)` is a scheme of characteristic `p`. -/
instance instIsCharP_adjoinRootAlphaP_spec
    (R : Type u) [CommRing R] [CharP R p] (c : R) :
    Scheme.IsCharP (Spec (.of (AdjoinRoot (Polynomial.X ^ p - Polynomial.C c)))) p :=
  inferInstance

/-- A morphism of schemes in characteristic `p` is an `α_p`-cover when it is
isomorphic to `Spec(R[z] / (z^p - c)) ⟶ Spec(R)` for some commutative ring `R`
and some element `c`. -/
class IsAlphaPCover {X Y : Scheme.{u}} [Scheme.IsCharP X p] [Scheme.IsCharP Y p]
    (f : X ⟶ Y) : Prop where
  /-- The morphism is isomorphic to an affine `α_p`-cover. -/
  exists_adjoinRoot :
    ∃ (R : Type u) (_ : CommRing R) (c : R)
      (eSrc : X ≅ Spec (.of (AdjoinRoot (Polynomial.X ^ p - Polynomial.C c))))
      (eTgt : Y ≅ Spec (.of R)),
      eSrc.hom ≫ adjoinRootAlphaPHom p R c = f ≫ eTgt.hom

/-- The affine `α_p`-cover is an `α_p`-cover. -/
instance instIsAlphaPCover_adjoinRoot (R : Type u) [CommRing R] [CharP R p] (c : R) :
    IsAlphaPCover p (adjoinRootAlphaPHom p R c) where
  exists_adjoinRoot :=
    ⟨R, inferInstance, c, Iso.refl _, Iso.refl _, rfl⟩

/-- A morphism is an `α_p`-cover exactly when it is isomorphic to
`Spec(R[z] / (z^p - c)) ⟶ Spec(R)`. -/
theorem isAlphaPCover_iff {X Y : Scheme.{u}} [Scheme.IsCharP X p] [Scheme.IsCharP Y p]
    (f : X ⟶ Y) :
    IsAlphaPCover p f ↔
      ∃ (R : Type u) (_ : CommRing R) (c : R)
        (eSrc : X ≅ Spec (.of (AdjoinRoot (Polynomial.X ^ p - Polynomial.C c))))
        (eTgt : Y ≅ Spec (.of R)),
        eSrc.hom ≫ adjoinRootAlphaPHom p R c = f ≫ eTgt.hom :=
  sorry

/-- Source-semantic specification of an `α_p`-cover: characteristic `p` on source
and target, together with an affine presentation `Spec(R[z] / (z^p - c)) ⟶ Spec(R)`. -/
theorem IsAlphaPCover.spec {X Y : Scheme.{u}} [Scheme.IsCharP X p]
    [Scheme.IsCharP Y p] (f : X ⟶ Y) :
    IsAlphaPCover p f ↔
      Scheme.IsCharP X p ∧ Scheme.IsCharP Y p ∧
        ∃ (R : Type u) (_ : CommRing R) (c : R)
          (eSrc : X ≅ Spec (.of (AdjoinRoot (Polynomial.X ^ p - Polynomial.C c))))
          (eTgt : Y ≅ Spec (.of R)),
          eSrc.hom ≫ adjoinRootAlphaPHom p R c = f ≫ eTgt.hom :=
  sorry

/-- An `α_p`-cover is finite locally free. -/
theorem isFiniteLocallyFree_ofIsAlphaPCover {X Y : Scheme.{u}}
    [Scheme.IsCharP X p] [Scheme.IsCharP Y p] (f : X ⟶ Y)
    [IsAlphaPCover p f] : IsFiniteLocallyFree f :=
  sorry

/-- An `α_p`-cover has constant rank `p`. -/
instance instIsFiniteLocallyFreeOfRank_ofIsAlphaPCover {X Y : Scheme.{u}}
    [Scheme.IsCharP X p] [Scheme.IsCharP Y p] (f : X ⟶ Y)
    [IsAlphaPCover p f] : IsFiniteLocallyFreeOfRank f p :=
  sorry

/-- A finite composition of `α_p`-covers. -/
inductive IsFiniteCompositionOfAlphaPCover :
    {X Y : Scheme.{u}} → (X ⟶ Y) → Prop
  | ofAlphaP {X Y : Scheme.{u}} [Scheme.IsCharP X p] [Scheme.IsCharP Y p]
      (f : X ⟶ Y) : IsAlphaPCover p f →
      IsFiniteCompositionOfAlphaPCover f
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

/-- Source-semantic specification of an iterated `α_p`-cover: characteristic `p`
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

end AlgebraicGeometry
