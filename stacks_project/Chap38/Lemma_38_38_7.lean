/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.FrobeniusColimit.StructureSheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 38.38.7 (1): for a prime `p`, the sequential Frobenius colimit of a
commutative `ZMod p`-algebra is its absolute weak normalization. -/
@[stacks 0EVW]
#check (Ring.FrobeniusColimit.instIsIsoToAbsoluteWeakNormalization :
  ∀ (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] [Algebra (ZMod p) A],
    IsIso
      (terminal.from (Ring.FrobeniusColimit.asAbsoluteWeakNormalizationAlgebra p A) :
        Ring.FrobeniusColimit.asAbsoluteWeakNormalizationAlgebra p A ⟶
          ⊤_ (AlgebraicGeometry.AbsoluteWeakNormalizationAlgebras A)))

/- Lemma 38.38.7 (2): over a characteristic-`p` base, the canonical map from the
structure presheaf to the Frobenius-colimit h-sheaf is an h-sheafification. -/
@[stacks 0EVW]
#check
  (AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit.structureToSheaf_isSheafification :
    ∀ (p : ℕ) [Fact p.Prime]
      (Schh : AlgebraicGeometry.ChosenBigHSite.{u, u}) (S : Schh.carrier)
      [AlgebraicGeometry.Scheme.IsCharP (Schh.toScheme.obj S) p],
      Presheaf.IsSheafification
        (AlgebraicGeometry.ChosenBigHSite.bigTopology Schh S)
        (AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit.structureToSheaf p Schh S))

/- Lemma 38.38.7 (2): on a quasi-compact and quasi-separated represented object,
the canonical comparison from the Frobenius colimit of global sections to the
Frobenius-colimit h-sheaf value is an isomorphism. -/
@[stacks 0EVW]
#check (AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit.instIsIsoSectionsToSheaf :
  ∀ (p : ℕ) [Fact p.Prime]
    (Schh : AlgebraicGeometry.ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [AlgebraicGeometry.Scheme.IsCharP (Schh.toScheme.obj S) p]
    (U : CategoryTheory.Over S)
    [CompactSpace ((AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S).obj U)]
    [QuasiSeparatedSpace
      ((AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S).obj U)],
    IsIso
      (AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit.sectionsToSheaf p Schh S U))
