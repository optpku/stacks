/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RationalSingularity.Resolution
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace IsRationalSingularity

/- Lemma 54.9.8: a two-dimensional rational singularity admitting a dualizing complex
has a finite sequence of blowups at singular closed points whose post-initial stages are
normal and whose terminal scheme has an invertible dualizing module. -/
@[stacks 0BBV] #check
  (IsRationalSingularity.existsSingularPointBlowupSequence :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    (h_dualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizing),
    ∃ (X : Scheme.{u})
      (s : Scheme.SingularPointBlowupSequence (Spec (.of A)) X)
      (hX : IsLocallyNoetherian X) (ωX : X.Modules),
      s.EveryTarget (fun Y ↦ Y.isNormal) ∧
        @Scheme.IsDualizingModule X hX ωX ∧ Scheme.Modules.Invertible ωX)

end IsRationalSingularity
