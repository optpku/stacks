module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.List.TFAE
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap68.Lemma_68_18_6_Fibre
public import stacks_project.Chap68.Lemma_68_18_10_Fibre

/-!
# Generically finite morphisms of algebraic spaces, reprise

For a quasi-separated locally finite-type morphism of algebraic spaces with
quasi-separated target, finiteness of the set-theoretic fibre over a
codimension-zero point is equivalent to finiteness of a field-valued fibre
and to the existence of open subspaces on which the restriction is finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.21.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
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
theorem tfae_finite_fiberOver_fieldFiber_exists_isFinite_restrict {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsAbsolutelyQuasiSeparated Y] (p : FieldValuedPoint Y)
    (hy : localRingDimAt (Points.mk p) = 0) :
    List.TFAE
      [ (fiberOver f (Points.mk p)).Finite
      , Finite (Points (fieldFiber f p))
      , ∃ (X' : OpenSubspace X) (Y' : OpenSubspace Y) (g : X'.X ⟶ Y'.X),
          g ≫ Y'.ι = X'.ι ≫ f ∧ Points.mk p ∈ Y'.pointsSet ∧
            fiberOver f (Points.mk p) ⊆ X'.pointsSet ∧ IsFinite g ] :=
  sorry

/-- Finiteness of the set-theoretic fibre over a codimension-zero point is
equivalent to finiteness of the points of a field-valued fibre representing
that point. -/
theorem finite_fiberOver_iff_finite_fieldFiber {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsAbsolutelyQuasiSeparated Y] (p : FieldValuedPoint Y)
    (hy : localRingDimAt (Points.mk p) = 0) :
    (fiberOver f (Points.mk p)).Finite ↔ Finite (Points (fieldFiber f p)) :=
  sorry

/-- Finiteness of the points of a field-valued fibre over a codimension-zero
point is equivalent to the existence of open subspaces of the source and
target, containing the fibre and the point, on which `f` restricts to a finite
morphism. -/
theorem finite_fieldFiber_iff_exists_isFinite_restrict {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsAbsolutelyQuasiSeparated Y] (p : FieldValuedPoint Y)
    (hy : localRingDimAt (Points.mk p) = 0) :
    Finite (Points (fieldFiber f p)) ↔
      ∃ (X' : OpenSubspace X) (Y' : OpenSubspace Y) (g : X'.X ⟶ Y'.X),
        g ≫ Y'.ι = X'.ι ≫ f ∧ Points.mk p ∈ Y'.pointsSet ∧
          fiberOver f (Points.mk p) ⊆ X'.pointsSet ∧ IsFinite g :=
  sorry

/-- Finiteness of the set-theoretic fibre over a codimension-zero point is
equivalent to the existence of open subspaces of the source and target,
containing the fibre and the point, on which `f` restricts to a finite
morphism. -/
theorem finite_fiberOver_iff_exists_isFinite_restrict {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsAbsolutelyQuasiSeparated Y] (p : FieldValuedPoint Y)
    (hy : localRingDimAt (Points.mk p) = 0) :
    (fiberOver f (Points.mk p)).Finite ↔
      ∃ (X' : OpenSubspace X) (Y' : OpenSubspace Y) (g : X'.X ⟶ Y'.X),
        g ≫ Y'.ι = X'.ι ≫ f ∧ Points.mk p ∈ Y'.pointsSet ∧
          fiberOver f (Points.mk p) ⊆ X'.pointsSet ∧ IsFinite g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
