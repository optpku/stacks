module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.GlobalSections.Equalizer

/-!
# Lemma 7.45.2

The coequalizer-to-equalizer transport is reusable global-sections
infrastructure.  Chapter 7 retains the source cofork and equalizer statements
as tagged recalls, while ReasLib owns the terminal and sheafified-Yoneda data.
-/

@[expose] public section

/- Lemma 7.45.2 (0792): the canonical terminal cofork of
`h[V]^# ⇉ h[U]^#` supplies the source-side coequalizer datum. -/
@[stacks 0792] #check @CategoryTheory.GrothendieckTopology.SheafifiedRepresentable.terminalCofork

@[stacks 0792] #check @CategoryTheory.Sheaf.ΓObjEquivCompatibleHom

@[stacks 0792] #check @CategoryTheory.Sheaf.existsUnique_globalSection_of_coequalizer
