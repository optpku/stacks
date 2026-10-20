module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.Point.Presheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.CategoryTheory.Sites.CategoryCohomology.Bar.DeltaFunctor
public import ReasLib.CategoryTheory.Sites.CategoryCohomology.Derived
public import ReasLib.CategoryTheory.Sites.Chaotic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computing category cohomology

The composable-arrow bar complex computes the right-derived limit of an additive presheaf.  On
the chaotic topology this identifies the entire functor `Sheaf.functorH` with bar cohomology,
functorially in the coefficient sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory.CategoryCohomology

variable {C : Type u} [Category.{v} C]
variable [UnivLE.{max u v, w}]

section DerivedComparison

variable [HasLimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]
variable [HasInjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat.{w})]

/-- Right-derived-limit category cohomology and bar cohomology are naturally isomorphic as
coefficient functors. -/
@[stacks 08RZ "derived-limit and bar category cohomology comparison"]
theorem functor_isomorphic_bar (n : ℕ) :
    IsIsomorphic (cohomologyFunctor (C := C) n)
      (Bar.cohomologyFunctor (C := C) n) := sorry

/-- The right-derived limit of a coefficient presheaf is computed by its bar complex. -/
@[stacks 08RZ "category cohomology computed by the bar complex"]
theorem isomorphic_barCohomology (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    IsIsomorphic (cohomology F n) (Bar.cohomology F n) := sorry

end DerivedComparison

namespace Chaotic

/-- The category-cohomology bar complex functor on sheaves for the chaotic topology. -/
@[stacks 08RZ "chaotic-site category-cohomology bar complex"]
noncomputable abbrev complexFunctor :
    Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{w} ⥤
      CochainComplex AddCommGrpCat.{w} ℕ :=
  sheafToPresheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{w} ⋙
    Bar.complexFunctor (C := C)

/-- The explicit category-cohomology bar complex of a sheaf on the chaotic topology. -/
@[stacks 08RZ "chaotic-site category-cohomology complex"]
noncomputable abbrev complex
    (F : Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{w}) :
    CochainComplex AddCommGrpCat.{w} ℕ :=
  (complexFunctor (C := C)).obj F

/-- Bar cohomology as a functor on sheaves for the chaotic topology. -/
@[stacks 08RZ "chaotic-site bar cohomology functor"]
noncomputable abbrev cohomologyFunctor (n : ℕ) :
    Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
  sheafToPresheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{w} ⋙
    Bar.cohomologyFunctor (C := C) n

/-- The bar-cohomology object of a sheaf on the chaotic topology. -/
@[stacks 08RZ "chaotic-site bar cohomology object"]
noncomputable abbrev cohomology
    (F : Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{w}) (n : ℕ) :
    AddCommGrpCat.{w} :=
  (cohomologyFunctor (C := C) n).obj F

/-- The chaotic-site bar complex is exact in its coefficient sheaf. -/
@[stacks 08RZ "exactness of the chaotic-site category-cohomology complex"]
theorem complexFunctor_exact :
    exactFunctor (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{w})
      (CochainComplex AddCommGrpCat.{w} ℕ) (complexFunctor (C := C)) := sorry

section Point

variable [LocallySmall.{w} C]

/-- A point skyscraper sheaf has zero positive-degree bar cohomology. -/
@[stacks 08RZ "point-skyscraper bar acyclicity"]
theorem pointSkyscraper_cohomology_isZero_of_pos
    (U : C) (A : AddCommGrpCat.{w}) {n : ℕ} (hn : 0 < n) :
    IsZero (cohomology ((GrothendieckTopology.pointBot.{w} U).skyscraperSheafFunctor.obj A) n) :=
  sorry

end Point

section SheafCohomology

variable [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{w}]
variable [HasExt (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{w})]

/-- Example 21.42.1 (Computing cohomology) (08RZ): on the chaotic topology, the sheaf
cohomology functor is naturally isomorphic to the cohomology of the composable-arrow bar complex. -/
@[stacks 08RZ]
theorem functor_isomorphic (n : ℕ) :
    IsIsomorphic (Sheaf.functorH (⊥ : GrothendieckTopology C) n)
      (cohomologyFunctor (C := C) n) := sorry

/-- Objectwise form of the chaotic-site category-cohomology computation. -/
@[stacks 08RZ "objectwise chaotic-site category-cohomology computation"]
theorem isomorphic_homology_complex
    (F : Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{w}) (n : ℕ) :
    IsIsomorphic ((Sheaf.functorH (⊥ : GrothendieckTopology C) n).obj F)
      ((complex F).homology n) := sorry

variable [LocallySmall.{w} C]

/-- Point skyscraper sheaves on the chaotic topology have zero positive sheaf cohomology. -/
@[stacks 08RZ "point-skyscraper sheaf-cohomology acyclicity"]
theorem pointSkyscraper_sheafCohomology_isZero_of_pos
    (U : C) (A : AddCommGrpCat.{w}) {n : ℕ} (hn : 0 < n) :
    IsZero ((Sheaf.functorH (⊥ : GrothendieckTopology C) n).obj
      ((GrothendieckTopology.pointBot.{w} U).skyscraperSheafFunctor.obj A)) := sorry

end SheafCohomology

end Chaotic

end CategoryTheory.CategoryCohomology
