/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence.Source
import StacksCheckRecall

@[expose] public section

/-!
# Example 21.32.1

The two spectral sequences are the generic source Hyper-Ext constructions, specialized to the
Grothendieck abelian category of modules on a ringed site.  Their predicates retain the displayed
page, the Ext abutment, and convergence under the source bounded-above and target bounded-below
hypotheses; no second spectral-sequence datum is chosen in this chapter.
-/

open CategoryTheory

/- Example 21.32.1 (07AA) (1): the cohomology filtration gives the renumbered spectral sequence
with `E₂^{i,j} = Extⁱ(H⁻ʲ(K), F)`. -/
@[stacks 07AA "(1) source cohomology spectral sequence"] #check
  @DerivedCategory.Ext.Source.Cohomology.existsSpectralSequence

#check @DerivedCategory.Ext.Source.Cohomology.IsSpectralSequence.pageTwo
#check @DerivedCategory.Ext.Source.Cohomology.IsSpectralSequence.convergesAfterRenumbering

/- Example 21.32.1 (07AA) (2): the stupid filtration gives the spectral sequence with
`E₁^{i,j} = Extʲ(K⁻ⁱ, F)`. -/
@[stacks 07AA "(2) source stupid-filtration spectral sequence"] #check
  @DerivedCategory.Ext.Source.Stupid.existsSpectralSequence

#check @DerivedCategory.Ext.Source.Stupid.IsSpectralSequence.pageOne
#check @DerivedCategory.Ext.Source.Stupid.IsSpectralSequence.converges

end
