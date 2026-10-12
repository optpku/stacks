/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family.Blowup
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.80.2: a quasi-compact, quasi-separated scheme with finitely many irreducible
components admits a quasi-compact dense open and an admissible blowup carrying an ample family
of invertible modules. -/
@[stacks 0GTT] #check
  (AlgebraicGeometry.Scheme.Modules.AmpleFamily.exists_admissibleBlowup :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [Finite (irreducibleComponents X)],
      ∃ (U : X.Opens) (X' : AlgebraicGeometry.Scheme.{u}) (b : X' ⟶ X),
        AlgebraicGeometry.QuasiCompact U.ι ∧ Dense (U : Set X) ∧
          AlgebraicGeometry.IsAdmissibleBlowup U b ∧
            ∃ (ι : Type u) (L : ι → X'.Modules),
              AlgebraicGeometry.Scheme.Modules.AmpleFamily L)
