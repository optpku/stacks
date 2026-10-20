/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.GenericallyFinite
import StacksCheckRecall

/-!
# Generically finite morphisms of algebraic spaces, reprise

For a quasi-separated locally finite-type morphism of algebraic spaces with
quasi-separated target, finiteness of the set-theoretic fibre over a
codimension-zero point is equivalent to finiteness of a field-valued fibre
and to the existence of open subspaces on which the restriction is finite.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 68.21.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume that `f` is quasi-separated and locally of
finite type and `Y` quasi-separated. Let `y ∈ |Y|` be a point of
codimension `0` on `Y`. The following are equivalent: the set `f⁻¹({y})` is
finite; the space `|X_k|` is finite where `Spec(k) ⟶ Y` represents `y`;
there exist open subspaces `X' ⊂ X` and `Y' ⊂ Y` with `f(X') ⊂ Y'`,
`y ∈ |Y'|`, and `f⁻¹({y}) ⊂ |X'|` such that the restriction `X' ⟶ Y'` is
finite.

Here `y` is `Points.mk p` for a field-valued representative `p` with `p.hom`
playing the role of `Spec(k) ⟶ Y`, `|X_k|` is `Points (fieldFiber f p)`,
`f⁻¹({y})` is `fiberOver f (Points.mk p)`, a point of codimension `0` means
`localRingDimAt (Points.mk p) = 0`, `|Y'|` and `|X'|` are `Y'.pointsSet`
and `X'.pointsSet`, and the restriction `X' ⟶ Y'` is a morphism
`g : X'.X ⟶ Y'.X` satisfying `g ≫ Y'.ι = X'.ι ≫ f`. -/
@[stacks 0AD0]
#check (AlgebraicGeometry.AlgebraicSpace.tfae_finite_fiberOver_fieldFiber_exists_isFinite_restrict :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsAbsolutelyQuasiSeparated Y] (p : FieldValuedPoint Y)
    (hy : localRingDimAt (Points.mk p) = 0),
    List.TFAE
      [ (fiberOver f (Points.mk p)).Finite
      , Finite (Points (fieldFiber f p))
      , ∃ (X' : OpenSubspace X) (Y' : OpenSubspace Y) (g : X'.X ⟶ Y'.X),
          g ≫ Y'.ι = X'.ι ≫ f ∧ Points.mk p ∈ Y'.pointsSet ∧
            fiberOver f (Points.mk p) ⊆ X'.pointsSet ∧ IsFinite g ])

#check (AlgebraicGeometry.AlgebraicSpace.finite_fiberOver_iff_finite_fieldFiber :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsAbsolutelyQuasiSeparated Y] (p : FieldValuedPoint Y)
    (hy : localRingDimAt (Points.mk p) = 0),
    (fiberOver f (Points.mk p)).Finite ↔ Finite (Points (fieldFiber f p)))

#check (AlgebraicGeometry.AlgebraicSpace.finite_fieldFiber_iff_exists_isFinite_restrict :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsAbsolutelyQuasiSeparated Y] (p : FieldValuedPoint Y)
    (hy : localRingDimAt (Points.mk p) = 0),
    Finite (Points (fieldFiber f p)) ↔
      ∃ (X' : OpenSubspace X) (Y' : OpenSubspace Y) (g : X'.X ⟶ Y'.X),
        g ≫ Y'.ι = X'.ι ≫ f ∧ Points.mk p ∈ Y'.pointsSet ∧
          fiberOver f (Points.mk p) ⊆ X'.pointsSet ∧ IsFinite g)

#check (AlgebraicGeometry.AlgebraicSpace.finite_fiberOver_iff_exists_isFinite_restrict :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsAbsolutelyQuasiSeparated Y] (p : FieldValuedPoint Y)
    (hy : localRingDimAt (Points.mk p) = 0),
    (fiberOver f (Points.mk p)).Finite ↔
      ∃ (X' : OpenSubspace X) (Y' : OpenSubspace Y) (g : X'.X ⟶ Y'.X),
        g ≫ Y'.ι = X'.ι ≫ f ∧ Points.mk p ∈ Y'.pointsSet ∧
          fiberOver f (Points.mk p) ⊆ X'.pointsSet ∧ IsFinite g)

