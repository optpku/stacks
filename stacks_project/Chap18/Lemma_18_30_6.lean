/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Basis.Presentation
public import ReasLib.CategoryTheory.Sites.EnoughObjects.Presentation
import StacksCheckRecall

@[expose] public section

/- Lemma 18.30.6 (1): enough basis objects give a locally surjective map from a coproduct of
sheafified representables to every sheaf of sets. -/
@[stacks 093B "(1)"]
#check @CategoryTheory.Coverage.HasEnoughObjectsWithProperty.existsSheafifiedRepresentableCover

/- Lemma 18.30.6 (2): enough basis objects give an epimorphism from a coproduct of localized
structure modules to every module sheaf. -/
@[stacks 093B "(2)"]
#check @SheafOfModules.Localization.Basis.existsEpiFromCoproduct

/- Sieve-saturated specializations remain available for Grothendieck-topology inputs. -/
#check @CategoryTheory.GrothendieckTopology.HasEnoughObjectsWithProperty.existsSheafifiedRepresentableCover
#check @SheafOfModules.Localization.Basis.exists_epi_from_coproduct
