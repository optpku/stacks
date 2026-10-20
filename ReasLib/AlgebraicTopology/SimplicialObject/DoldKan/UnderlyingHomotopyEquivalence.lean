module

public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv.Functor
public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv.QuasiIso
public import ReasLib.AlgebraicTopology.SimplicialObject.Underlying.HomotopyEquivalence
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
@stack 08P2

# Underlying homotopy equivalences of simplicial abelian groups

For simplicial abelian groups, a homotopy equivalence after forgetting to simplicial sets induces
quasi-isomorphisms on both the alternating-face and normalized Moore complexes. This is stronger
than preservation of additive simplicial homotopy equivalences: the chosen underlying homotopies
need not be additive.
-/

@[expose] public section

open CategoryTheory HomologicalComplex
open AlgebraicTopology

universe u

namespace CategoryTheory.SimplicialObject

namespace AddCommGrp

namespace underlying

/-- The specialization to additive commutative groups of the general morphism property detected
by an underlying functor to types. -/
@[stacks 08P2 "underlying homotopy equivalences of simplicial abelian groups"]
abbrev homotopyEquivalences :
    MorphismProperty (SimplicialObject AddCommGrpCat.{u}) :=
  Underlying.homotopyEquivalences (forget AddCommGrpCat)

/-- A simplicial additive-group map is an underlying homotopy equivalence exactly when its
underlying simplicial-set map is a simplicial homotopy equivalence. -/
@[simp, stacks 08P2 "membership in underlying homotopy equivalences"]
theorem homotopyEquivalences_iff {X Y : SimplicialObject AddCommGrpCat.{u}}
    (f : X ⟶ Y) :
    AddCommGrp.underlying.homotopyEquivalences f ↔
      IsHomotopyEquivalence (Functor.whiskerRight f (forget AddCommGrpCat)) := sorry

namespace homotopyEquivalences

namespace alternatingFace

/-- Underlying simplicial-set homotopy equivalences of simplicial abelian groups induce
alternating-face quasi-isomorphisms. -/
@[stacks 08P2 "associated chain complex"]
theorem le_quasiIso :
    AddCommGrp.underlying.homotopyEquivalences ≤
      (HomologicalComplex.quasiIso AddCommGrpCat.{u} (ComplexShape.down ℕ)).inverseImage
        (alternatingFaceMapComplex AddCommGrpCat.{u}) := sorry

end alternatingFace

namespace normalizedMoore

/-- Underlying simplicial-set homotopy equivalences of simplicial abelian groups induce
normalized-Moore quasi-isomorphisms. -/
@[stacks 08P2]
theorem le_quasiIso :
    AddCommGrp.underlying.homotopyEquivalences ≤
      (HomologicalComplex.quasiIso AddCommGrpCat.{u} (ComplexShape.down ℕ)).inverseImage
        (normalizedMooreComplex AddCommGrpCat.{u}) := sorry

end normalizedMoore
end homotopyEquivalences

end underlying

end AddCommGrp

end CategoryTheory.SimplicialObject
