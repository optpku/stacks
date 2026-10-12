/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Factorization
import StacksCheckRecall

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.43.3 (Zariski's Main Theorem): a quasi-finite separated morphism to a
quasi-compact quasi-separated scheme factors as a quasi-compact open immersion followed by a
finite morphism. -/
@[stacks 05K0] #check
  (AlgebraicGeometry.Scheme.Hom.QuasiFinite.exists_openImmersion_finiteFactorization :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiFinite f] [IsSeparated f]
      [CompactSpace S] [QuasiSeparatedSpace S],
      ∃ (T : Scheme.{u}) (j : X ⟶ T) (π : T ⟶ S),
        QuasiCompact j ∧ IsOpenImmersion j ∧ IsFinite π ∧ j ≫ π = f)

end AlgebraicGeometry.Scheme.Hom
