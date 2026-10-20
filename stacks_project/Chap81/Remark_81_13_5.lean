module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.EssentiallyConstant
import StacksCheckRecall

/-!
# Remark 81.13.5

In Situation 81.13.2 with `X` quasi-compact, Lemma 81.13.4 means the sequential
coequalizer system is essentially constant with value `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Remark 81.13.5: in Situation 81.13.2 with `X` quasi-compact, Lemma 81.13.4
means the sequential coequalizer system `X₁ ⟶ X₂ ⟶ X₃ ⟶ ⋯` is essentially
constant with value `X`, in the sense of Categories, Definition 4.22.1. -/
@[stacks 0AGL] #check
  (AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.cocone_isEssentiallyConstant :
    ∀ {S : Scheme.{u}} {X X' Z : AlgebraicSpace S}
    (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X] [IsQuasiCompact X]
    [IsClosedImmersion i] [Proper f]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)),
    (AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.cocone f i h_iso).IsEssentiallyConstant)
