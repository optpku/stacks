module

public import ReasLib.CategoryTheory.Sites.Cech.AcyclicIntersections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Injectivity of degree-one Čech comparisons

This leaf exposes the torsor-level consequence as a statement about the normalized comparison
relation.  It does not force a torsor implementation into the Čech API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {U : C} {ι : Type w} [HasFiniteProducts (Over U)]
variable [HasProducts AddCommGrpCat.{v}]
variable [HasWeakSheafify J AddCommGrpCat.{v}]
variable [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
variable
  [Functor.HasRightDerivedFunctor
    ((siteAbelianSectionsFunctor J U).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{v}))]

/-- Lemma 21.10.4 (0A6G): a normalized degree-one Čech-to-site comparison is injective for a
covering family. -/
@[stacks 0A6G "injectivity of a degree-one Cech comparison"]
theorem cechCohomologyToSiteCohomology_injective_degree_one
    (V : ι → Over U) (hV : (J.over U).CoversTop V)
    (G : Sheaf J AddCommGrpCat.{v})
    (f : (cechCohomologyOnSheaves J V 1).obj G ⟶ G.H' 1 U)
    (hf : Cech.IsComparison V 1 G f) :
    Function.Injective f :=
  sorry

/-- A normalized degree-one comparison is injective once its family covers the target object. -/
theorem Cech.IsComparison.injective_degree_one
    {V : ι → Over U} {G : Sheaf J AddCommGrpCat.{v}}
    {f : (cechCohomologyOnSheaves J V 1).obj G ⟶ G.H' 1 U}
    (hf : Cech.IsComparison V 1 G f)
    (hV : (J.over U).CoversTop V) :
    Function.Injective f :=
  sorry

/-- A normalized degree-one comparison is a monomorphism once its family covers the target. -/
theorem Cech.IsComparison.mono_degree_one
    {V : ι → Over U} {G : Sheaf J AddCommGrpCat.{v}}
    {f : (cechCohomologyOnSheaves J V 1).obj G ⟶ G.H' 1 U}
    (hf : Cech.IsComparison V 1 G f)
    (hV : (J.over U).CoversTop V) :
    Mono f :=
  sorry

end CategoryTheory
