/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.DoldKan.DegenerateDecomposition.Canonical
public import ReasLib.AlgebraicTopology.DoldKan.DegenerateDecomposition.Degreewise
public import ReasLib.AlgebraicTopology.DoldKan.DegenerateComplex.Comparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison of canonical and degreewise Dold--Kan decompositions

This leaf is the only layer that identifies the canonical `QInfty` image summand with the explicit
degreewise degenerate complex.  The two decompositions themselves live in the sibling leaves.

@stack 019A
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open scoped Simplicial DoldKan

noncomputable section

universe v u

namespace AlgebraicTopology.DoldKan

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace QInfty.decomposition

/-- Replacing the canonical projector-image summand by the degreewise degenerate complex gives an
isomorphism between the two decomposition targets. -/
@[stacks 019A "canonical and degreewise degenerate summand comparison"]
noncomputable def degenerateIso :
    (normalizedMooreComplex A) ⊞ QInfty.imageFunctor (C := A) ≅
      (normalizedMooreComplex A) ⊞ degenerateComplex.functor (C := A) :=
  biprod.mapIso (Iso.refl _) (QInfty.imageComparison.natIso (C := A))

/-- The objectwise comparison obtained from the component of the natural summand comparison. -/
@[stacks 019A "objectwise degenerate-summand comparison"]
noncomputable def degenerateIso.eval (U : SimplicialObject A) :
    N[U] ⊞ QInfty.image U ≅ N[U] ⊞ D[U] :=
  (QInfty.decomposition.evalIso U).symm ≪≫
    (degenerateIso (A := A)).app U ≪≫
    (degenerateComplex.decomposition.evalIso U)

/-- The evaluated summand comparison is the identity on the normalized summand and the canonical
projector-image comparison on the degenerate summand. -/
@[stacks 019A "component of the degenerate summand comparison"]
theorem degenerateIso.app (U : SimplicialObject A) :
    degenerateIso.eval U =
      biprod.mapIso (Iso.refl N[U]) (QInfty.imageComparison.iso U) := sorry

end QInfty.decomposition

namespace degenerateComplex

namespace decomposition

/-- The source-facing objectwise decomposition is the canonical projector-image decomposition
followed by replacement of its image summand. -/
@[stacks 019A "source-facing decomposition through the canonical image"]
theorem eq_canonical (U : SimplicialObject A) :
    decomposition U = QInfty.decomposition U ≪≫
      QInfty.decomposition.degenerateIso.eval U := sorry

/-- The source-facing functorial decomposition is the canonical decomposition followed by the
natural replacement of the projector-image summand. -/
@[stacks 019A "source-facing natural decomposition through the canonical image"]
theorem natIso.eq_canonical :
    natIso (A := A) = QInfty.decomposition.natIso (A := A) ≪≫
      QInfty.decomposition.degenerateIso (A := A) := sorry

/-- The componentwise form of the source-facing and canonical functorial decomposition comparison.
-/
@[stacks 019A "componentwise source-facing canonical decomposition comparison"]
theorem natIso.app_eq_canonical (U : SimplicialObject A) :
    (natIso (A := A)).app U =
      (QInfty.decomposition.natIso (A := A) ≪≫
        QInfty.decomposition.degenerateIso (A := A)).app U := sorry

end decomposition

end degenerateComplex

end AlgebraicTopology.DoldKan
