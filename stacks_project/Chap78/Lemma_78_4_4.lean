module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Points
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Lemma 78.4.4: let `B → S` as in Section 78.3. Let `j : R ⟶ U ×_B U` be a
pre-relation of algebraic spaces over `B`. The relation on `|U|` given by
`x ∼ y` iff there exists `r` in `|R|` with `t(r) = x` and `s(r) = y` is an
equivalence relation whenever `j` is a pre-equivalence relation. -/
@[stacks 043F] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.pointsRel_equivalence :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U),
      P.IsPreEquivalence → Equivalence (PreRelation.pointsRel P))
