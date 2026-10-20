module

public import ReasLib.RingTheory.Henselian.Henselization.Presentation.PointedEtale
import StacksCheckRecall

@[expose] public section

/-!
# Etale neighborhoods of a prime

The prime-localized henselization presentation is owned by
`IsHenselizationOf.PointedEtale`.  This source-facing file retains the three
claims of Lemma 10.155.7 as direct recalls; no chapter-local category,
localization map, residue-field equivalence, lift, or colimit witness is
introduced.

@stack 04GV
-/

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace Chap10

variable {R : Type u} [CommRing R]
variable (p : Ideal R) [p.IsPrime]

/- Lemma 10.155.7 (1), tag `04GV`: the category of pairs `(S, q)` with
`R → S` etale, `q` over `p`, and `κ(q) = κ(p)` is filtered.  The formal
category is the canonical pointed-etale category over `p.ResidueField`. -/
@[stacks 04GV]
#check @CommAlgCat.Over.Etale.AtPrime.category
@[stacks 04GV]
#check @CommAlgCat.Over.Etale.instIsFiltered

/- Lemma 10.155.7 (2), tag `04GV`: the source diagram `(S, q) ↦ S` has a
chosen henselization of `Localization.AtPrime p` as a colimit.  The shared
owner states this as `Nonempty (IsColimit ...)`, the Prop-valued interface
appropriate before proof-stage choice of a universal-property witness. -/
@[stacks 04GV]
#check @CommAlgCat.Over.Etale.AtPrime.sourceDiagram
@[stacks 04GV]
#check @IsHenselizationOf.PointedEtale.Presentation.sourceCocone
@[stacks 04GV]
#check @IsHenselizationOf.PointedEtale.Presentation.sourceIsColimit

/- Lemma 10.155.7 (3), tag `04GV`: the localized diagram `(S, q) ↦ S_q`
has the same henselization as a colimit. -/
@[stacks 04GV]
#check @CommAlgCat.Over.Etale.AtPrime.localizedDiagram
@[stacks 04GV]
#check @IsHenselizationOf.PointedEtale.Presentation.cocone
@[stacks 04GV]
#check @IsHenselizationOf.PointedEtale.Presentation.isColimit

end Chap10
