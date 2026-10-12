/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Invariant.FixedPoints
public import ReasLib.RingTheory.Invariant.Ideal

@[expose] public section

/-!
# Invariant ideals and fixed points of quotients

This leaf owns the quotient-side construction for a group action on a commutative ring.  The
stability proof is an explicit input because it is proof-dependent data; the resulting action is
named and reusable, but is not registered as a global instance for every arbitrary proof.
Finite-group spectral consequences for the induced fixed-points map live in the companion
`Invariant.Quotient.Spectrum` leaf.
@stack 09EG
-/

open PrimeSpectrum
open scoped Pointwise

universe u v

namespace Ideal

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [MulSemiringAction G R]

namespace Quotient

/-- Stability gives the containment needed to descend an action map to the quotient. -/
@[stacks 09EG "stable ideal quotient action"]
theorem le_comap_smul (I : Ideal R) (hI : I.IsStable G) (g : G) :
    I ≤ Ideal.comap (MulSemiringAction.toRingHom G R g) I := sorry
-- Proof strategy: rewrite `hI g` using `Ideal.pointwise_smul_def`, then apply
-- `Ideal.map_le_iff_le_comap` to the resulting equality of the image of `I` with `I`.

/-- The ring endomorphism induced by a group element on a stable ideal quotient. -/
@[stacks 09EG "quotient action ring hom"]
def smulHom (I : Ideal R) (hI : I.IsStable G) (g : G) : R ⧸ I →+* R ⧸ I :=
  Ideal.quotientMap I (MulSemiringAction.toRingHom G R g) (le_comap_smul I hI g)

/-- The quotient action map evaluated on a quotient representative. -/
@[simp, stacks 09EG "quotient action on representatives"]
theorem smulHom_mk (I : Ideal R) (hI : I.IsStable G) (g : G) (x : R) :
    smulHom I hI g (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (g • x) := sorry
-- Proof strategy: unfold `smulHom` and apply the representative computation rule
-- `Ideal.quotientMap_mk`; the underlying action ring hom sends `x` to `g • x` definitionally.

/-- The identity element induces the identity endomorphism of a stable ideal quotient. -/
@[simp, stacks 09EG "identity quotient action"]
theorem smulHom_one (I : Ideal R) (hI : I.IsStable G) :
    smulHom I hI (1 : G) = 1 := sorry
-- Proof strategy: use `Ideal.Quotient.ringHom_ext` and evaluate both maps on
-- `Ideal.Quotient.mk I x`; rewrite with `smulHom_mk` and `one_smul`.

/-- Multiplication in the acting group becomes composition of quotient endomorphisms. -/
@[stacks 09EG "composition of quotient action maps"]
theorem smulHom_mul (I : Ideal R) (hI : I.IsStable G) (g h : G) :
    smulHom I hI (g * h) = (smulHom I hI g).comp (smulHom I hI h) := sorry
-- Proof strategy: use `Ideal.Quotient.ringHom_ext`, evaluate on quotient representatives, rewrite
-- all three occurrences with `smulHom_mk`, and finish with `mul_smul`.

/-- The quotient endomorphisms, bundled as a monoid homomorphism. -/
@[stacks 09EG "quotient action monoid hom"]
def actionHom (I : Ideal R) (hI : I.IsStable G) : G →* (R ⧸ I →+* R ⧸ I) where
  toFun := smulHom I hI
  map_one' := smulHom_one I hI
  map_mul' := smulHom_mul I hI

/-- The induced group action on the quotient by a stable ideal. -/
@[reducible, stacks 09EG "group action on stable ideal quotient"]
def action (I : Ideal R) (hI : I.IsStable G) : MulSemiringAction G (R ⧸ I) :=
  MulSemiringAction.compHom (R ⧸ I) (actionHom I hI)

section FixedPoints

variable (I : Ideal R) (hI : I.IsStable G)

/-- The quotient map as an equivariant ring homomorphism for the induced quotient action. -/
@[stacks 09EG "equivariant quotient map"]
def mkHom :
    -- Local instance justification (defeq pin): the codomain action is the explicit action
    -- determined by this stable ideal.
    letI := action I hI
    R →+*[G] R ⧸ I :=
  -- Local instance justification (defeq pin): the equivariance field must use the same quotient
  -- action as the result type.
  letI := action I hI
  { toRingHom := Ideal.Quotient.mk I
    map_smul' := fun g x ↦ smulHom_mk I hI g x }

/-- The kernel condition used to factor the equivariant map through the fixed-point quotient. -/
@[stacks 09EG "fixed-point quotient lift condition"]
theorem fixedPointsMap_zero :
    -- Local instance justification (defeq pin): fixed points are formed for the named quotient
    -- action determined by `hI`.
    letI := action I hI
    ∀ x : FixedPoints.subring R G,
      x ∈ Ideal.comap (FixedPoints.subring R G).subtype I →
        (mkHom I hI).fixedPoints x = 0 := sorry
-- Proof strategy: introduce `x` and its comap membership, apply `Subtype.ext`, unfold the
-- underlying map of `mkHom`, and use `Ideal.Quotient.eq_zero_iff_mem` for the representative `x`.

/-- The canonical map from the quotient of the fixed subring to the fixed subring of the quotient. -/
@[stacks 09EG "fixed points of a stable quotient"]
def fixedPointsMap :
    -- Local instance justification (defeq pin): the target fixed subring must retain the explicit
    -- quotient action selected by `hI`.
    letI := action I hI
    FixedPoints.subring R G ⧸
        Ideal.comap (FixedPoints.subring R G).subtype I →+*
      FixedPoints.subring (R ⧸ I) G :=
  -- Local instance justification (defeq pin): the lift and its codomain use that same action.
  letI := action I hI
  Ideal.Quotient.lift (Ideal.comap (FixedPoints.subring R G).subtype I)
    (mkHom I hI).fixedPoints (fixedPointsMap_zero I hI)

/-- The fixed-point quotient map on a representative. -/
@[simp, stacks 09EG "fixed-point quotient representative"]
theorem fixedPointsMap_mk (x : FixedPoints.subring R G) :
    -- Local instance justification (defeq pin): this computation is for the action owned by
    -- `action I hI`.
    letI := action I hI
    ((fixedPointsMap I hI
        (Ideal.Quotient.mk (Ideal.comap (FixedPoints.subring R G).subtype I) x)) : R ⧸ I) =
      Ideal.Quotient.mk I x := sorry
-- Proof strategy: unfold `fixedPointsMap` and rewrite the quotient lift on a representative with
-- `Ideal.Quotient.lift_mk`; coercion from the target fixed-point subtype then exposes `mkHom`.

/-- The fixed-point quotient map composed with the quotient projection is the restricted equivariant
map. -/
@[stacks 09EG "fixed-point quotient composition"]
theorem fixedPointsMap_comp_mk :
    -- Local instance justification (defeq pin): both maps must elaborate with the identical
    -- proof-dependent quotient action.
    letI := action I hI
    (fixedPointsMap I hI).comp
        (Ideal.Quotient.mk (Ideal.comap (FixedPoints.subring R G).subtype I)) =
      (mkHom I hI).fixedPoints := sorry
-- Proof strategy: extensionality on `x : FixedPoints.subring R G`, apply `Subtype.ext`, and use
-- `fixedPointsMap_mk`; both sides then reduce to `Ideal.Quotient.mk I x`.

end FixedPoints

namespace FixedPoints

/-- The canonical map from the quotient of the fixed subring into the fixed points of a stable
quotient has trivial kernel. No finiteness hypothesis on the acting group is needed. -/
@[stacks 09EG "fixed-point quotient kernel"]
theorem map_ker (I : Ideal R) (hI : I.IsStable G) :
    RingHom.ker (Ideal.Quotient.fixedPointsMap I hI) = ⊥ := sorry
-- Proof strategy: prove both inclusions.  For a kernel element, choose a fixed-subring
-- representative with `Ideal.Quotient.mk_surjective`, coerce its zero image from the fixed
-- subring of `R ⧸ I` to `R ⧸ I`, rewrite using `fixedPointsMap_mk`, and translate vanishing back
-- through `Ideal.Quotient.eq_zero_iff_mem`; this is exactly membership in the source comap ideal.

/-- The canonical map from the quotient of the fixed subring into the fixed points of a stable
quotient is injective. -/
@[stacks 09EG "fixed-point quotient injectivity"]
theorem map_injective (I : Ideal R) (hI : I.IsStable G) :
    Function.Injective (Ideal.Quotient.fixedPointsMap I hI) := sorry
-- Proof strategy: apply `RingHom.injective_iff_ker_eq_bot` and discharge the kernel equality with
-- `map_ker I hI`.

end FixedPoints

end Quotient

end Ideal
