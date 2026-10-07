module

public import ReasLib.RingTheory.Completion.CohenStructure.Presentation
import StacksCheckRecall

@[expose] public section

/-!
# Cohen Structure Presentations

@stack 032D
-/

/- Lemma 10.160.11: the reusable finite regular complete-local source package. -/
@[stacks 032D "canonical Cohen structure"]
#check @IsCompleteLocalRing.exists_cohenStructure

/- Lemma 10.160.11: the source-facing subring and its field/Cohen-ring power-series
presentation. -/
@[stacks 032D "power-series Cohen subring"]
#check @IsCompleteLocalRing.exists_powerSeries_cohenSubring
