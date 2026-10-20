module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.KFlat.Resolution
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.17.11

The ringed-site K-flat resolution is a reusable ReasLib owner stated with canonical complex
predicates.  The chapter item is a recall surface and keeps both the termwise-epi and complex-epi
forms available to downstream chapters.
-/

open SheafOfModules.RingedSite

/- Lemma 21.17.11 (06YS) (1): a K-flat, termwise-flat replacement with termwise-epic comparison. -/
@[stacks 06YS "termwise-epimorphic K-flat resolution"] #check
  @exists_termwiseEpi_quasiIso_from_KFlat_complex_of_flat_terms

/- Lemma 21.17.11 (06YS) (2): the comparison can equivalently be packaged as an epic complex
morphism. -/
@[stacks 06YS "epimorphic K-flat resolution"] #check
  @exists_epi_quasiIso_from_KFlat_complex_of_flat_terms
