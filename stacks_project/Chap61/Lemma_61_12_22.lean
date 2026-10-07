module

public import stacks_project.Chap61.Lemma_61_12_20_Affine
public import stacks_project.Chap61.Lemma_61_12_22_Instances
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import StacksCheckRecall

/-!
# Lemma 61.12.22

The pro-étale topology on each of the five pro-étale sites of a scheme is
subcanonical.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

section

variable (S : Scheme.{u})

/- Lemma 61.12.22 (1): the topology on Sch_proétale is subcanonical. -/
@[stacks 098Z] #check
  (inferInstance : (Scheme.proetaleTopology : GrothendieckTopology Scheme.{u}).Subcanonical)

/- Lemma 61.12.22 (2): the topology on S_proétale is subcanonical. -/
@[stacks 098Z] #check
  (inferInstance : (Scheme.ProEt.topology S).Subcanonical)

/- Lemma 61.12.22 (3): the topology on (Sch/S)_proétale is subcanonical. -/
@[stacks 098Z] #check
  (inferInstance : (Scheme.proetaleTopology.over S).Subcanonical)

/- Lemma 61.12.22 (4): the topology on S_affine,proétale is subcanonical. -/
@[stacks 098Z] #check
  (inferInstance : (Scheme.ProEt.affineTopology S).Subcanonical)

end

section

variable (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier)

/- Lemma 61.12.22 (5): the topology on (Aff/S)_proétale is subcanonical. -/
@[stacks 098Z] #check
  (inferInstance : (ChosenBigProetaleSite.bigAffineTopology X S).Subcanonical)

end
