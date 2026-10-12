/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.ChangeOfBase
import StacksCheckRecall

/-!
# Lemma 15.83.7

@stack 0DHQ
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

/-!
# Lemma 15.83.7 compatibility entry point

The pseudo-coherent-ring-map comparison between relative and absolute
pseudo-coherence is owned by
`ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.ChangeOfBase`.
-/

/- Lemma 15.83.7 (1), tag `0DHQ`: relative and absolute `m`-pseudo-coherence agree over a
pseudo-coherent ring map. -/
@[stacks 0DHQ "(1), relative and absolute m-pseudo-coherence"]
#check fun {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [(algebraMap R A).IsPseudoCoherentRingMap]
    (K : DerivedCategory (ModuleCat A)) (m : ℤ) =>
  (CategoryTheory.DerivedCategory.isMPseudoCoherentRelativeTo_iff_isMPseudoCoherent_of_isPseudoCoherentRingMap
    K m : K.IsMPseudoCoherentRelativeTo R m ↔ K.IsMPseudoCoherent m)

/- Lemma 15.83.7 (2), tag `0DHQ`: relative and absolute pseudo-coherence agree over a
pseudo-coherent ring map. -/
@[stacks 0DHQ "(2), relative and absolute pseudo-coherence"]
#check fun {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [(algebraMap R A).IsPseudoCoherentRingMap] (K : DerivedCategory (ModuleCat A)) =>
  (CategoryTheory.DerivedCategory.isPseudoCoherentRelativeTo_iff_isPseudoCoherent_of_isPseudoCoherentRingMap
    K : K.IsPseudoCoherentRelativeTo R ↔ K.IsPseudoCoherent)
