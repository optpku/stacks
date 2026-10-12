/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree.Components
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 33.44.6: for a proper scheme of dimension at most one over a field, the degree of a
finite locally free module is the multiplicity-weighted sum of its degrees on the reduced
one-dimensional irreducible-component subschemes. -/
@[stacks 0AYW] #check
  (AlgebraicGeometry.Scheme.Modules.curveDegree.eq_sum_irreducibleComponents :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (hdim : topologicalKrullDim X ≤ 1) (ℰ : X.Modules) (n : ℕ)
      [Scheme.Modules.IsFiniteLocallyFreeOfRank n ℰ],
      -- Local instance justification (proof-local temporary data): properness over a field gives
      -- finite type, so the canonical finite-type theorem supplies global Noetherianity.
      let _ : IsNoetherian X := Scheme.Hom.FiniteType.isNoetherian f
      -- Local instance justification (proof-local temporary data): a Noetherian space has finitely
      -- many irreducible components.
      let _ : Finite (irreducibleComponents X) :=
        AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
      -- Local instance justification (noncanonical choice): the finite component type is
      -- enumerated only in order to form the finite sum.
      let _ : Fintype (irreducibleComponents X) := Fintype.ofFinite (irreducibleComponents X)
      Scheme.Modules.curveDegree f hdim ℰ n =
        Finset.sum
          ((Finset.univ.filter fun Z : irreducibleComponents X ↦
            topologicalKrullDim (X.irreducibleComponentSubscheme Z) = 1).attach) fun Z ↦
          (X.irreducibleComponentMultiplicity Z.1 : ℤ) *
            Scheme.Modules.curveDegree (X.irreducibleComponentSubschemeι Z.1 ≫ f)
              (((Finset.mem_filter.mp Z.2).2).le)
              ((Scheme.Modules.pullback (X.irreducibleComponentSubschemeι Z.1)).obj ℰ) n)
