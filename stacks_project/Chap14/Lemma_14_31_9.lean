module

public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.UnderlyingHomotopyEquivalence
import StacksCheckRecall

/-!
@stack 08P2

# Source-facing recall for Lemma 14.31.9

An underlying simplicial-set homotopy equivalence of simplicial abelian groups induces a
quasi-isomorphism on the associated alternating-face complex. The equivalent normalized-Moore
form remains available as a canonical companion.
-/

@[expose] public section

open CategoryTheory HomologicalComplex
open AlgebraicTopology

universe u

namespace CategoryTheory.SimplicialObject

variable {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)

#check HomotopyEquiv.whiskerRight

#check AddCommGrp.underlying.homotopyEquivalences

/- The property is the additive-commutative-group specialization of the reusable detector for
an arbitrary functor to types. -/
#check (Underlying.homotopyEquivalences (forget AddCommGrpCat.{u}) :
  MorphismProperty (SimplicialObject AddCommGrpCat.{u}))

#check Underlying.homotopyEquivalences_comp

#check AddCommGrp.underlying.homotopyEquivalences.alternatingFace.le_quasiIso

/- Lemma 14.31.9: an underlying simplicial-set homotopy equivalence induces a quasi-isomorphism
on the associated alternating-face complex. -/
@[stacks 08P2]
#check (AddCommGrp.underlying.homotopyEquivalences.alternatingFace.le_quasiIso f :
  IsHomotopyEquivalence (Functor.whiskerRight f (forget AddCommGrpCat)) →
    QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f))

/- Canonical equivalent formulation using the normalized Moore complex. -/
#check (AddCommGrp.underlying.homotopyEquivalences.normalizedMoore.le_quasiIso f :
  IsHomotopyEquivalence (Functor.whiskerRight f (forget AddCommGrpCat)) →
    QuasiIso ((normalizedMooreComplex AddCommGrpCat.{u}).map f))

end CategoryTheory.SimplicialObject
