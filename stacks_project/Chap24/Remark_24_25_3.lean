module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.KInjective.HomComplex
import StacksCheckRecall

/-!
# Remark 24.25.3

A graded-injective DG target makes enriched Hom contravariantly exact on every short exact
sequence, not only on admissible sequences.  The resulting long exact cohomology sequence is
then Mathlib's canonical homology sequence for the explicit enriched-Hom short complex.
-/

@[expose] public section

open CategoryTheory
open HomologicalComplex.HomologySequence
open SheafOfModules.RingedSite.DifferentialGradedModule

/- Remark 24.25.3 (0FSQ): an arbitrary short exact sequence of DG modules becomes a short exact
sequence of enriched Hom complexes after precomposition into a graded-injective target. -/
@[stacks 0FSQ] #check @HomComplex.precomp_shortExact

/- The reusable owner exposes the actual contravariant Hom-complex short complex. -/
#check @HomComplex.precompShortComplex

/- Its connecting morphism and exactness clauses are the standard Mathlib homology-sequence
operations; no chapter-owned long-exact package is introduced. -/
#check @ShortComplex.ShortExact.δ
#check @ShortComplex.ShortExact.homology_exact₁
#check @ShortComplex.ShortExact.homology_exact₂
#check @ShortComplex.ShortExact.homology_exact₃
#check @composableArrows₅
#check @composableArrows₅_exact
