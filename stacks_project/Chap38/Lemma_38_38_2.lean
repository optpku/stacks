/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.FrobeniusColimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 38.38.2 (1): the canonical map from the sectionwise Frobenius colimit presents
the associated ring-valued h-sheaf as its sheafification for the chosen big h topology. -/
@[stacks 0EVK] #check
  (AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit.toSheaf_isSheafification :
    ∀ (p : ℕ) [Fact p.Prime]
      (Schh : AlgebraicGeometry.ChosenBigHSite.{u, u}) (S : Schh.carrier)
      [AlgebraicGeometry.Scheme.IsCharP (Schh.toScheme.obj S) p],
      Presheaf.IsSheafification
        (AlgebraicGeometry.ChosenBigHSite.bigTopology Schh S)
        (AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit.toSheaf p Schh S))

/- Lemma 38.38.2 (2): on every quasi-compact and quasi-separated represented object,
the canonical comparison from the Frobenius colimit of global sections to the associated
ring-valued h-sheaf value is an isomorphism. -/
@[stacks 0EVK] #check
  (AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit.instIsIsoSectionsToSheaf :
    ∀ (p : ℕ) [Fact p.Prime]
      (Schh : AlgebraicGeometry.ChosenBigHSite.{u, u}) (S : Schh.carrier)
      [AlgebraicGeometry.Scheme.IsCharP (Schh.toScheme.obj S) p] (U : Over S)
      [CompactSpace ((AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S).obj U)]
      [QuasiSeparatedSpace ((AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S).obj U)],
      IsIso
        (AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit.sectionsToSheaf p Schh S U))
