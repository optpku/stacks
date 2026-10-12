/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Koszul.Total
import StacksCheckRecall

universe u

/- Lemma 36.9.3: the total powered-Koszul Hom-colimit complex is canonically isomorphic to
the total alternating Cech complex, functorially in the coefficient complex. -/
@[stacks 08D1] #check
  (LocalizedModule.Away.Cech.Koszul.homColimitTotalIso :
    ∀ {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A),
      LocalizedModule.Away.Cech.Koszul.homColimitTotal f ≅
        LocalizedModule.Away.Cech.Alternating.total f)
