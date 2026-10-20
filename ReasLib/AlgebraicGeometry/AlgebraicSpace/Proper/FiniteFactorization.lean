module

public import Mathlib.Data.Set.Finite.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-!
# Neighbourhood finite factorizations of proper families

In a commutative triangle of algebraic spaces over a scheme, a proper morphism
to the base whose special fibre (or set-theoretic fibre, when the base is
decent) has finite image in the target of a separated locally finite-type map
factors, after shrinking the base, through a closed subspace finite over that
neighbourhood.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Let `S` be a scheme. Let `h : X ⟶ Y`, `f : X ⟶ B`,
`g : Y ⟶ B` be a commutative triangle of morphisms of algebraic spaces over
`S`. Assume `f` is proper and `g` is separated and locally of finite type.
Let `p` be a field-valued point of `B`. If the image of `|X_k| ⟶ |Y_k|` is
finite, then there is an open subspace `B' ⊂ B` containing `Points.mk p` such
that `X_{B'} ⟶ Y_{B'}` factors through a closed subspace `Z ⊂ Y_{B'}` finite
over `B'`.

Here `overBaseChange h g p.hom` is the comparison `|X_k| ⟶ |Y_k|`, and
`overBaseChange h g ι` is `X_{B'} ⟶ Y_{B'}`. The identification of
`pullback (h ≫ g)` with `pullback f` uses `hcomm`. -/
@[stacks 0AEJ]
theorem exists_isFinite_factor_of_finite_fieldFiber_image
    {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (h : X ⟶ Y) (f : X ⟶ B) (g : Y ⟶ B) (hcomm : h ≫ g = f)
    [Proper f] [Separated g] [LocallyOfFiniteType g] (p : FieldValuedPoint B)
    (hfin : (Set.range (Points.map (overBaseChange h g p.hom))).Finite) :
    ∃ (B' : AlgebraicSpace S) (ι : B' ⟶ B) (hι : IsOpenImmersion ι)
      (Z : AlgebraicSpace S) (ιZ : Z ⟶ pullback g ι)
      (toZ : pullback (h ≫ g) ι ⟶ Z),
      Points.mk p ∈ Set.range (Points.map ι) ∧ IsClosedImmersion ιZ ∧
        toZ ≫ ιZ = overBaseChange h g ι ∧
        IsFinite (ιZ ≫ pullback.snd g ι) :=
  sorry

/-- Let `S` be a scheme. Let `h : X ⟶ Y`, `f : X ⟶ B`,
`g : Y ⟶ B` be a commutative triangle of morphisms of algebraic spaces over
`S`. Assume `f` is proper, `g` is separated and locally of finite type, and
`B` is decent. Let `b` be a point of `B`. If the image of `|f|⁻¹({b})` in
`|Y|` is finite, then there is an open subspace `B' ⊂ B` containing `b` such
that `X_{B'} ⟶ Y_{B'}` factors through a closed subspace `Z ⊂ Y_{B'}` finite
over `B'`.

Here `Set.image (Points.map h) (fiberOver f b)` is the image of the
set-theoretic fibre in `|Y|`, and `overBaseChange h g ι` is
`X_{B'} ⟶ Y_{B'}`. The identification of `pullback (h ≫ g)` with
`pullback f` uses `hcomm`. -/
@[stacks 0AEJ]
theorem exists_isFinite_factor_of_finite_fiberOver_image
    {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (h : X ⟶ Y) (f : X ⟶ B) (g : Y ⟶ B) (hcomm : h ≫ g = f)
    [Proper f] [Separated g] [LocallyOfFiniteType g] [IsDecent B] (b : Points B)
    (hfin : (Set.image (Points.map h) (fiberOver f b)).Finite) :
    ∃ (B' : AlgebraicSpace S) (ι : B' ⟶ B) (hι : IsOpenImmersion ι)
      (Z : AlgebraicSpace S) (ιZ : Z ⟶ pullback g ι)
      (toZ : pullback (h ≫ g) ι ⟶ Z),
      b ∈ Set.range (Points.map ι) ∧ IsClosedImmersion ιZ ∧
        toZ ≫ ιZ = overBaseChange h g ι ∧
        IsFinite (ιZ ≫ pullback.snd g ι) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
