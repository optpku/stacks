/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.ExtendNat.Homology
public import ReasLib.CategoryTheory.Sites.Cech.Sheaf
public import ReasLib.CategoryTheory.Sites.Derived.Sections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Cech-to-site cohomology comparisons

The primary datum is one natural transformation of bounded-below derived-category-valued
coefficient functors.  Its source homology identification is canonical; a degree system fixes the
target identifications in every nonnegative degree at once.  Keeping one derived morphism in the
public bundle prevents unrelated maps in different degrees from being mistaken for one comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe w v u

namespace CategoryTheory.Cech

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {U : C} {ι : Type w} [HasFiniteProducts (Over U)]
variable [HasProducts AddCommGrpCat.{v}]
variable [HasWeakSheafify J AddCommGrpCat.{v}]
variable [HasSheafify J AddCommGrpCat.{v}]
variable
  [(siteAbelianSectionsFunctor J U).mapHomotopyCategoryPlus.comp
      DerivedCategory.Plus.Qh |>.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{v}))]

/-- The nonnegative Cech complex, extended by zero and localized in
`D⁺(AddCommGrpCat)`, functorially in the coefficient sheaf. -/
@[stacks 03AX "derived Cech source"]
abbrev derivedSource (J : GrothendieckTopology C) (U : C)
    [HasFiniteProducts (Over U)] {ι : Type w} (family : ι → Over U)
    [HasProducts AddCommGrpCat.{v}] :
    Sheaf J AddCommGrpCat.{v} ⥤ DerivedCategory.Plus AddCommGrpCat.{v} :=
  sheafToPresheaf J AddCommGrpCat.{v} ⋙
    cechComplexOnPresheaves U family ⋙
    CochainComplex.Plus.extendNat AddCommGrpCat.{v} ⋙
    DerivedCategory.Plus.Q

/-- Derived sections over `U`, restricted to coefficient sheaves placed in degree zero. -/
@[stacks 03AX "derived site-cohomology target"]
abbrev derivedTarget (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [HasSheafify J AddCommGrpCat.{v}]
    [Functor.HasRightDerivedFunctor
      ((siteAbelianSectionsFunctor J U).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{v}))] :
    Sheaf J AddCommGrpCat.{v} ⥤ DerivedCategory.Plus AddCommGrpCat.{v} :=
  sheafToBoundedBelowDerivedSectionsFunctor J U

/-- A Cech-to-site comparison is a single coefficient-natural morphism in the bounded-below
derived category whose degree-zero homology map is invertible. -/
@[stacks 03AX "derived Cech-to-site comparison"]
structure DerivedComparison (J : GrothendieckTopology C) (U : C)
    [HasFiniteProducts (Over U)] {ι : Type w} (family : ι → Over U)
    [HasProducts AddCommGrpCat.{v}]
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [HasSheafify J AddCommGrpCat.{v}]
    [(siteAbelianSectionsFunctor J U).mapHomotopyCategoryPlus.comp
        DerivedCategory.Plus.Qh |>.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{v}))] where
  /-- The comparison, natural in the coefficient sheaf. -/
  hom : derivedSource J U family ⟶ derivedTarget J U
  /-- The induced degree-zero comparison is an isomorphism. -/
  homologyZero_isIso (F : Sheaf J AddCommGrpCat.{v}) :
    IsIso ((Functor.whiskerRight hom
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} 0)).app F)

/-- Lemma 21.10.3 (03AX): a covering family admits a Cech-to-site comparison natural in
abelian-sheaf coefficients. -/
@[stacks 03AX "existence of a derived Cech-to-site comparison"]
theorem derivedComparison_nonempty (family : ι → Over U)
    (hfamily : (J.over U).CoversTop family) :
    Nonempty (DerivedComparison J U family) := sorry

namespace DerivedComparison

/-- Applying degree-`n` homology to a derived comparison gives a natural transformation of
coefficient functors. -/
noncomputable def homology {family : ι → Over U}
    (alpha : DerivedComparison J U family) (n : ℤ) :
    derivedSource J U family ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n ⟶
      derivedTarget J U ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n :=
  Functor.whiskerRight alpha.hom
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n)

end DerivedComparison

/-- In nonnegative degree, homology of the derived Cech source canonically recovers the ordinary
Cech cohomology functor on sheaves. -/
@[stacks 03AX "homology of the derived Cech source"]
noncomputable def derivedSourceHomologyIso (family : ι → Over U) (p : ℕ) :
    derivedSource J U family ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} (p : ℤ) ≅
      cechCohomologyOnSheaves J family p :=
  Functor.isoWhiskerLeft
    (sheafToPresheaf J AddCommGrpCat.{v} ⋙ cechComplexOnPresheaves U family)
    (CochainComplex.Plus.extendNatDerivedHomologyIso AddCommGrpCat.{v} p)

omit [HasFiniteProducts (Over U)] [HasProducts AddCommGrpCat.{v}] in
/-- In nonnegative degree, homology of the derived target recovers objectwise site cohomology. -/
@[stacks 03AX "homology of the derived site-cohomology target"]
theorem derivedTarget_homology_isIsomorphic
    [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] (p : ℕ) :
    IsIsomorphic
      (derivedTarget J U ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} (p : ℤ))
      (Sheaf.cohomologyPresheafFunctor J p ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op U)) := sorry

/-- A degree-`p` Cech-to-site comparison is a coefficient-natural morphism from ordinary Cech
cohomology to site cohomology over `U`. -/
@[stacks 03AX "degreewise Cech-to-site comparison"]
abbrev DegreeComparison (J : GrothendieckTopology C) (U : C)
    [HasFiniteProducts (Over U)] {ι : Type w} (family : ι → Over U)
    [HasProducts AddCommGrpCat.{v}]
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] (p : ℕ) :=
  cechCohomologyOnSheaves J family p ⟶
    Sheaf.cohomologyPresheafFunctor J p ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op U)

namespace DerivedComparison

/-- One derived comparison together with explicit target homology identifications in every
nonnegative degree.  The source identification is the canonical `derivedSourceHomologyIso`. -/
@[stacks 03AX "degreewise Cech-to-site comparison system"]
structure DegreeSystem (J : GrothendieckTopology C) (U : C)
    [HasFiniteProducts (Over U)] {ι : Type w} (family : ι → Over U)
    [HasProducts AddCommGrpCat.{v}]
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [HasSheafify J AddCommGrpCat.{v}]
    [(siteAbelianSectionsFunctor J U).mapHomotopyCategoryPlus.comp
        DerivedCategory.Plus.Qh |>.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{v}))]
    [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] where
  /-- The comparison in the bounded-below derived category. -/
  comparison : DerivedComparison J U family
  /-- Identification of derived-target homology with site cohomology over `U`. -/
  targetIso (p : ℕ) :
    derivedTarget J U ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} (p : ℤ) ≅
      Sheaf.cohomologyPresheafFunctor J p ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op U)

namespace DegreeSystem

/-- The ordinary degree-`p` comparison induced by a fixed derived comparison system. -/
noncomputable def degreeComparison [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    {family : ι → Over U} (S : DegreeSystem J U family) (p : ℕ) :
    DegreeComparison J U family p :=
  (derivedSourceHomologyIso (J := J) family p).inv ≫
    S.comparison.homology (p : ℤ) ≫
    (S.targetIso p).hom

/-- The degree-zero comparison of a normalized system is invertible at every coefficient sheaf. -/
theorem degreeComparison_zero_isIso_app [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    {family : ι → Over U} (S : DegreeSystem J U family)
    (F : Sheaf J AddCommGrpCat.{v}) :
    IsIso ((S.degreeComparison 0).app F) := sorry

end DegreeSystem

/-- A covering family admits one comparison system in all nonnegative degrees. -/
theorem degreeSystem_nonempty (family : ι → Over U)
    (hfamily : (J.over U).CoversTop family)
    [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] :
    Nonempty (DegreeSystem J U family) := sorry

end DerivedComparison

/-- A morphism from Cech cohomology to site cohomology is a comparison map when it is an
object-component of a degreewise comparison arising from one derived comparison. -/
@[stacks 03AX "Cech-to-site comparison map"]
def IsComparison [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    (family : ι → Over U) (p : ℕ) (F : Sheaf J AddCommGrpCat.{v})
    (f : (cechCohomologyOnSheaves J family p).obj F ⟶ F.H' p U) : Prop :=
  ∃ S : DerivedComparison.DegreeSystem J U family,
    f = (S.degreeComparison p).app F

/-- The component of a degreewise comparison is a Cech-to-site comparison map. -/
theorem DerivedComparison.DegreeSystem.isComparison
    [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    {family : ι → Over U} (S : DerivedComparison.DegreeSystem J U family) (p : ℕ)
    (F : Sheaf J AddCommGrpCat.{v}) :
    IsComparison family p F ((S.degreeComparison p).app F) := sorry

/-- A covering family has a Cech-to-site comparison map in every nonnegative degree. -/
theorem comparison_exists (family : ι → Over U)
    (hfamily : (J.over U).CoversTop family)
    [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    (p : ℕ) (F : Sheaf J AddCommGrpCat.{v}) :
    ∃ f : (cechCohomologyOnSheaves J family p).obj F ⟶ F.H' p U,
      IsComparison family p F f := sorry

end CategoryTheory.Cech
