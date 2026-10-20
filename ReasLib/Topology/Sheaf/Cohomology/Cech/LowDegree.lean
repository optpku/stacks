module

public import ReasLib.Topology.Sheaf.Cohomology.Cech.ColimitComparison
public import ReasLib.Topology.Presheaf.Cech.Comparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The degree-one global Cech comparison

The reusable API keeps the coverwise comparison map and its torsor-class specification explicit.
Invertibility is a theorem about that data, rather than a field hidden in a witness.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.Cohomology.Cech.DegreeOne

variable {X : TopCat.{u + 1}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (X.Sheaf AddCommGrpCat.{u + 1})]

/-!
`ClassMap` is the class-valued target map used in the cover comparison predicate.  Keeping it as
a plain function lets a site-specific classification theorem (for example, a torsor/H¹
equivalence) be supplied without forcing this Cech layer to import that theorem's owner.
-/

/-- The degree-one map from torsor isomorphism classes to the global sheaf-cohomology target. -/
@[stacks 09V1 "degree-one torsor class map for Cech comparison"]
abbrev ClassMap : Type _ :=
  ∀ F : X.Sheaf AddCommGrpCat.{u + 1},
    CategoryTheory.Sheaf.Torsor.IsoClasses
      (CategoryTheory.Sheaf.toSheafOfGroups
        (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
          AddCommGrpCat.{u + 1})) →
      (targetCohomology.{0, u, u + 1} X 1).obj F

/-!
The coverwise predicate is the source-facing semantic contract: at every indexed open cover and
coefficient sheaf, the chosen stage map is injective and has exactly the image of classes trivial on
that cover.  It does not assert that the induced colimit map is invertible.
-/

/-- A degree-one refinement comparison has the prescribed torsor-class image on every cover. -/
@[stacks 09V1 "degree-one coverwise Cech comparison specification"]
def IsCoverwise (κ : ClassMap (X := X))
    (c : RefinementComparison.{0, u, u + 1} X 1) : Prop :=
  ∀ (U : OpenCover.{u} X) (F : X.Sheaf AddCommGrpCat.{u + 1}),
    TopCat.Presheaf.Cech.Comparison.IsCoverComparison U.obj
      ((c.app U.refinementObject).app F) (κ F)

/-!
`CoverwiseComparison` is the reusable data owner.  Its fields contain only the explicit natural
comparison and its coverwise specification; the global `IsIso` instance is deliberately derived by
theorems below.
-/

/-- A degree-one Cech comparison together with its coverwise torsor-class specification. -/
@[stacks 09V1 "degree-one coverwise Cech comparison datum"]
structure CoverwiseComparison (κ : ClassMap (X := X)) where
  /-- The refinement- and coefficient-natural stage comparison. -/
  map : RefinementComparison.{0, u, u + 1} X 1
  /-- The stagewise injectivity and torsor-class image specification. -/
  coverwise : IsCoverwise (X := X) κ map

/-!
The global classification map must be bijective independently of the chosen coverwise stage
maps.  This is a separate hypothesis so that the Cech infrastructure can be reused with other
classifications and so no isomorphism proof is hidden in `CoverwiseComparison`.
-/

/-- The class map is bijective coefficientwise. -/
@[stacks 09V1 "bijective degree-one torsor class map"]
abbrev ClassMap.IsBijective (κ : ClassMap (X := X)) : Prop :=
  ∀ F : X.Sheaf AddCommGrpCat.{u + 1}, Function.Bijective (κ F)

/-- A coverwise degree-one comparison with a bijective class map satisfies the elementwise
filtered-colimit criterion. -/
@[stacks 09V1 "degree-one coverwise comparison satisfies the colimit criterion"]
theorem isColimitIso (κ : ClassMap (X := X))
    (hκ : ClassMap.IsBijective (X := X) κ)
    {c : RefinementComparison.{0, u, u + 1} X 1}
    (hc : IsCoverwise (X := X) κ c) :
    c.IsColimitIso := sorry

/-- The global map induced by a coverwise degree-one comparison with a bijective class map is an
isomorphism. -/
@[stacks 09V1 "degree-one global Cech comparison isomorphism"]
theorem comparison_isIso (κ : ClassMap (X := X))
    (hκ : ClassMap.IsBijective (X := X) κ)
    {c : RefinementComparison.{0, u, u + 1} X 1}
    (hc : IsCoverwise (X := X) κ c) :
    IsIso (comparison c) := sorry

namespace CoverwiseComparison

/-- Assemble a coverwise degree-one comparison from its map and certificate. -/
def ofMap {κ : ClassMap (X := X)}
    (map : RefinementComparison.{0, u, u + 1} X 1)
    (coverwise : IsCoverwise (X := X) κ map) :
    CoverwiseComparison (X := X) κ :=
  { map := map
    coverwise := coverwise }

/-- Regard a coverwise degree-one comparison with a bijective class map as a certified global
comparison. -/
@[stacks 09V1 "degree-one certified global Cech comparison"]
def toComparison {κ : ClassMap (X := X)}
    (c : CoverwiseComparison (X := X) κ)
    (hκ : ClassMap.IsBijective (X := X) κ) :
    Comparison.{0, u, u + 1} (X := X) 1 where
  map := c.map
  isColimitIso := DegreeOne.isColimitIso κ hκ c.coverwise

/-- The certified degree-one comparison carried by a coverwise comparison datum.  This is the
source-defined Cech-to-cohomology map used by the degree-one theorem. -/
abbrev canonicalComparison {κ : ClassMap (X := X)}
    (c : CoverwiseComparison (X := X) κ)
    (hκ : ClassMap.IsBijective (X := X) κ) :
    Comparison.{0, u, u + 1} (X := X) 1 :=
  c.toComparison hκ

/-- The functor-level isomorphism carried by a coverwise degree-one comparison. -/
@[stacks 09V1 "degree-one global Cech comparison of coefficient functors"]
noncomputable def iso {κ : ClassMap (X := X)}
    (c : CoverwiseComparison (X := X) κ)
    (hκ : ClassMap.IsBijective (X := X) κ) :
    cohomologyFunctor.{0, u, u + 1} X 1 ≅
      liftedTargetCohomology.{0, u, u + 1} X 1 :=
  (c.toComparison hκ).iso

/-- The component of the degree-one global Cech comparison at a coefficient sheaf. -/
@[stacks 09V1 "degree-one global Cech comparison at a coefficient sheaf"]
noncomputable def isoApp {κ : ClassMap (X := X)}
    (c : CoverwiseComparison (X := X) κ)
    (hκ : ClassMap.IsBijective (X := X) κ)
    (F : X.Sheaf AddCommGrpCat.{u + 1}) :
    cohomology.{0, u, u + 1} F 1 ≅
      (liftedTargetCohomology.{0, u, u + 1} X 1).obj F :=
  (c.iso hκ).app F

end CoverwiseComparison

/-- The source-defined degree-one Cech-to-cohomology map is an isomorphism. -/
@[stacks 09V1 "degree-one global Cech cohomology comparison"]
theorem isIsomorphic {κ : ClassMap (X := X)}
    (c : CoverwiseComparison (X := X) κ)
    (hκ : ClassMap.IsBijective (X := X) κ)
    (F : X.Sheaf AddCommGrpCat.{u + 1}) :
    IsIso ((comparison (CoverwiseComparison.canonicalComparison c hκ).map).app F) :=
  Comparison.isIso_app (CoverwiseComparison.canonicalComparison c hκ) F

end TopCat.Sheaf.Cohomology.Cech.DegreeOne
