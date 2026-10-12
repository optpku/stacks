/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Separation.Field
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 40.10.2: If the object scheme of a groupoid scheme is the spectrum of a field,
then its arrow scheme is separated. -/
@[stacks 04LN]
#check
  (AlgebraicGeometry.GroupoidScheme.isSeparatedArrowOfField :
    {S : Scheme.{u}} → (G : GroupoidScheme S) → {k : Type u} → [Field k] →
      (Spec (CommRingCat.of k) ≅ G.U.left) → Scheme.IsSeparated G.R.left)

end AlgebraicGeometry.GroupoidScheme
