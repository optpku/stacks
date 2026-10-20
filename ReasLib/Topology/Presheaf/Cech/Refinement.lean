module

public import ReasLib.CategoryTheory.Sites.Cech.Refinement
public import ReasLib.Topology.OpenCover.Refinement.Quotient
public import ReasLib.Topology.Presheaf.Cech.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Čech cohomology over the open-cover refinement category

This module first keeps selected open-cover refinements as raw morphisms on Čech complexes.
After passing to cohomology, parallel selections induce equal maps, so the coefficient-valued
diagram descends through `TopologicalSpace.OpenCover.RefinementCategory`.
-/

@[expose] public section

open AlgebraicTopology CategoryTheory TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe w v u

namespace TopCat.Presheaf.Cech

variable {X : TopCat.{u}}

/-- The Čech cochain complex of an indexed open cover, functorially in an additive presheaf. -/
abbrev complexInCoefficients (𝒰 : OpenCover.{v} X) :
    X.Presheaf AddCommGrpCat.{max u v w} ⥤
      CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  cechComplexFunctor 𝒰.obj

/-- The Čech cochain complex of an indexed open cover with fixed additive coefficients. -/
abbrev complex (𝒰 : OpenCover.{v} X)
    (F : X.Presheaf AddCommGrpCat.{max u v w}) :
    CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  (complexInCoefficients 𝒰).obj F

/-- Degree-`p` Čech cohomology of an indexed open cover, functorially in the coefficient
presheaf. -/
abbrev cohomologyInCoefficients (𝒰 : OpenCover.{v} X) (p : ℕ) :
    X.Presheaf AddCommGrpCat.{max u v w} ⥤ AddCommGrpCat.{max u v w} :=
  complexInCoefficients 𝒰 ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w}
      (ComplexShape.up ℕ) p

/-- Degree-`p` Čech cohomology of an indexed open cover with fixed additive coefficients. -/
abbrev cohomology (𝒰 : OpenCover.{v} X)
    (F : X.Presheaf AddCommGrpCat.{max u v w}) (p : ℕ) :
    AddCommGrpCat.{max u v w} :=
  (cohomologyInCoefficients 𝒰 p).obj F

/-- A selected open-cover refinement induces a coefficient-natural map of Čech complexes from
the coarse cover to the fine cover. -/
noncomputable abbrev complexMapNatTrans
    {𝒰 𝒱 : OpenCover.{v} X} (r : OpenCover.Refinement 𝒰 𝒱) :
    complexInCoefficients 𝒰 ⟶ complexInCoefficients 𝒱 :=
  formalCoproductCechComplexNatTransOfRefinement
    (A := AddCommGrpCat.{max u v w}) 𝒱.obj 𝒰.obj
      r.toFormalCoproductHom

/-- The Čech-complex map of a selected refinement with fixed additive coefficients. -/
abbrev complexMap {𝒰 𝒱 : OpenCover.{v} X}
    (r : OpenCover.Refinement 𝒰 𝒱)
    (F : X.Presheaf AddCommGrpCat.{max u v w}) :
    complex 𝒰 F ⟶ complex 𝒱 F :=
  (complexMapNatTrans r).app F

/-- The coefficient-natural Čech-complex map of the identity refinement is the identity. -/
theorem complexMapNatTrans_id (𝒰 : OpenCover.{v} X) :
    complexMapNatTrans (OpenCover.Refinement.id 𝒰) = 𝟙 _ := sorry

/-- Coefficient-natural Čech-complex maps respect composition of selected refinements. -/
theorem complexMapNatTrans_comp
    {𝒰 𝒱 𝒲 : OpenCover.{v} X}
    (r : OpenCover.Refinement 𝒰 𝒱) (s : OpenCover.Refinement 𝒱 𝒲) :
    complexMapNatTrans (OpenCover.Refinement.comp r s) =
      complexMapNatTrans r ≫ complexMapNatTrans s := sorry

/-- The raw open-cover refinement diagram of Čech complexes, functorially in additive
coefficients. -/
@[stacks 09UZ "coefficient-valued raw Cech-complex refinement diagram"]
noncomputable def complexFunctor (X : TopCat.{u}) :
    OpenCover.{v} X ⥤
      (X.Presheaf AddCommGrpCat.{max u v w} ⥤
        CochainComplex AddCommGrpCat.{max u v w} ℕ) where
  obj 𝒰 := complexInCoefficients 𝒰
  map r := complexMapNatTrans r
  map_id := complexMapNatTrans_id
  map_comp := fun r s ↦ complexMapNatTrans_comp r s

/-- The coefficient-valued raw complex diagram evaluates at a cover to its Čech-complex
functor. -/
@[simp]
theorem complexFunctor_obj (𝒰 : OpenCover.{v} X) :
    (complexFunctor X).obj 𝒰 = complexInCoefficients 𝒰 := sorry

/-- The map of the coefficient-valued raw complex diagram is the canonical selected-refinement
map. -/
@[simp]
theorem complexFunctor_map {𝒰 𝒱 : OpenCover.{v} X}
    (r : OpenCover.Refinement 𝒰 𝒱) :
    (complexFunctor X).map r = complexMapNatTrans r := sorry

/-- The raw open-cover refinement diagram of Čech complexes with one fixed coefficient
presheaf. -/
noncomputable def rawComplexDiagram
    (F : X.Presheaf AddCommGrpCat.{max u v w}) :
    OpenCover.{v} X ⥤ CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  complexFunctor X ⋙ (evaluation _ _).obj F

/-- The fixed-coefficient raw complex diagram evaluates to the expected coverwise Čech
complex. -/
@[simp]
theorem rawComplexDiagram_obj
    (F : X.Presheaf AddCommGrpCat.{max u v w}) (𝒰 : OpenCover.{v} X) :
    (rawComplexDiagram F).obj 𝒰 = complex 𝒰 F := sorry

/-- The fixed-coefficient raw complex diagram maps a selected refinement by its canonical Čech
complex map. -/
@[simp]
theorem rawComplexDiagram_map
    (F : X.Presheaf AddCommGrpCat.{max u v w})
    {𝒰 𝒱 : OpenCover.{v} X} (r : OpenCover.Refinement 𝒰 𝒱) :
    (rawComplexDiagram F).map r = complexMap r F := sorry

/-- A selected open-cover refinement induces a coefficient-natural map on Čech cohomology. -/
noncomputable abbrev cohomologyMapNatTrans
    {𝒰 𝒱 : OpenCover.{v} X} (r : OpenCover.Refinement 𝒰 𝒱) (p : ℕ) :
    cohomologyInCoefficients 𝒰 p ⟶ cohomologyInCoefficients 𝒱 p :=
  Functor.whiskerRight (complexMapNatTrans r)
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w}
      (ComplexShape.up ℕ) p)

/-- The Čech cohomology map of a selected refinement with fixed additive coefficients. -/
abbrev cohomologyMap {𝒰 𝒱 : OpenCover.{v} X}
    (r : OpenCover.Refinement 𝒰 𝒱)
    (F : X.Presheaf AddCommGrpCat.{max u v w}) (p : ℕ) :
    cohomology 𝒰 F p ⟶ cohomology 𝒱 F p :=
  (cohomologyMapNatTrans r p).app F

/-- The coefficient-natural Čech cohomology map of the identity refinement is the identity. -/
theorem cohomologyMapNatTrans_id (𝒰 : OpenCover.{v} X) (p : ℕ) :
    cohomologyMapNatTrans (OpenCover.Refinement.id 𝒰) p = 𝟙 _ := sorry

/-- Coefficient-natural Čech cohomology maps respect composition of selected refinements. -/
theorem cohomologyMapNatTrans_comp
    {𝒰 𝒱 𝒲 : OpenCover.{v} X}
    (r : OpenCover.Refinement 𝒰 𝒱) (s : OpenCover.Refinement 𝒱 𝒲) (p : ℕ) :
    cohomologyMapNatTrans (OpenCover.Refinement.comp r s) p =
      cohomologyMapNatTrans r p ≫ cohomologyMapNatTrans s p := sorry

/-- Parallel selected refinements induce equal coefficient-natural maps on Čech cohomology. -/
@[stacks 09UZ "independence of selected Cech cohomology refinement maps"]
theorem cohomologyMapNatTrans_eq
    {𝒰 𝒱 : OpenCover.{v} X} (r s : OpenCover.Refinement 𝒰 𝒱) (p : ℕ) :
    cohomologyMapNatTrans r p = cohomologyMapNatTrans s p := sorry

/-- Parallel selected refinements induce equal maps on Čech cohomology with fixed
coefficients. -/
theorem cohomologyMap_eq
    {𝒰 𝒱 : OpenCover.{v} X} (r s : OpenCover.Refinement 𝒰 𝒱)
    (F : X.Presheaf AddCommGrpCat.{max u v w}) (p : ℕ) :
    cohomologyMap r F p = cohomologyMap s F p := sorry

/-- The raw open-cover refinement diagram of degree-`p` Čech cohomology, functorially in
additive coefficients. -/
@[stacks 09UZ "coefficient-valued raw Cech-cohomology refinement diagram"]
noncomputable def cohomologyFunctor (X : TopCat.{u}) (p : ℕ) :
    OpenCover.{v} X ⥤
      (X.Presheaf AddCommGrpCat.{max u v w} ⥤ AddCommGrpCat.{max u v w}) where
  obj 𝒰 := cohomologyInCoefficients 𝒰 p
  map r := cohomologyMapNatTrans r p
  map_id := fun 𝒰 ↦ cohomologyMapNatTrans_id 𝒰 p
  map_comp := fun r s ↦ cohomologyMapNatTrans_comp r s p

/-- The coefficient-valued raw cohomology diagram evaluates to coverwise Čech cohomology. -/
@[simp]
theorem cohomologyFunctor_obj (𝒰 : OpenCover.{v} X) (p : ℕ) :
    (cohomologyFunctor X p).obj 𝒰 = cohomologyInCoefficients 𝒰 p := sorry

/-- The coefficient-valued raw cohomology diagram maps a selected refinement by its canonical
map on Čech cohomology. -/
@[simp]
theorem cohomologyFunctor_map
    {𝒰 𝒱 : OpenCover.{v} X} (r : OpenCover.Refinement 𝒰 𝒱) (p : ℕ) :
    (cohomologyFunctor X p).map r = cohomologyMapNatTrans r p := sorry

/-- The raw open-cover refinement diagram of degree-`p` Čech cohomology with one fixed
coefficient presheaf. -/
noncomputable def rawCohomologyDiagram
    (F : X.Presheaf AddCommGrpCat.{max u v w}) (p : ℕ) :
    OpenCover.{v} X ⥤ AddCommGrpCat.{max u v w} :=
  cohomologyFunctor X p ⋙ (evaluation _ _).obj F

/-- The fixed-coefficient raw cohomology diagram evaluates to coverwise Čech cohomology. -/
@[simp]
theorem rawCohomologyDiagram_obj
    (F : X.Presheaf AddCommGrpCat.{max u v w}) (p : ℕ) (𝒰 : OpenCover.{v} X) :
    (rawCohomologyDiagram F p).obj 𝒰 = cohomology 𝒰 F p := sorry

/-- The fixed-coefficient raw cohomology diagram maps a selected refinement by its canonical
map on Čech cohomology. -/
@[simp]
theorem rawCohomologyDiagram_map
    (F : X.Presheaf AddCommGrpCat.{max u v w}) (p : ℕ)
    {𝒰 𝒱 : OpenCover.{v} X} (r : OpenCover.Refinement 𝒰 𝒱) :
    (rawCohomologyDiagram F p).map r = cohomologyMap r F p := sorry

/-- The coefficient-valued raw cohomology diagram respects the relation identifying selected
refinements. -/
theorem cohomologyFunctor_map_eq_of_selection
    (X : TopCat.{u}) (p : ℕ) (𝒰 𝒱 : OpenCover.{v} X) (r s : 𝒰 ⟶ 𝒱)
    (h_selection : OpenCover.selectionRel X r s) :
    (cohomologyFunctor X p).map r = (cohomologyFunctor X p).map s := sorry

/-- Degree-`p` Čech cohomology over open covers as a coefficient-valued diagram on refinement
classes. -/
@[stacks 09UZ "coefficient-valued Cech-cohomology refinement diagram"]
noncomputable def refinementDiagram (X : TopCat.{u}) (p : ℕ) :
    OpenCover.RefinementCategory.{v} X ⥤
      (X.Presheaf AddCommGrpCat.{max u v w} ⥤ AddCommGrpCat.{max u v w}) :=
  CategoryTheory.Quotient.lift (OpenCover.selectionRel.{v} X)
    (cohomologyFunctor X p) (cohomologyFunctor_map_eq_of_selection X p)

/-- Evaluating the quotient refinement diagram at a represented cover recovers its
coefficient-valued Čech cohomology. -/
@[simp]
theorem refinementDiagram_obj (𝒰 : OpenCover.{v} X) (p : ℕ) :
    (refinementDiagram X p).obj 𝒰.refinementObject =
      cohomologyInCoefficients 𝒰 p := sorry

/-- On a represented selected refinement, the quotient diagram uses its canonical map on Čech
cohomology. -/
@[simp]
theorem refinementDiagram_map
    {𝒰 𝒱 : OpenCover.{v} X} (r : OpenCover.Refinement 𝒰 𝒱) (p : ℕ) :
    (refinementDiagram X p).map (OpenCover.refinementMap r) =
      cohomologyMapNatTrans r p := sorry

/-- The degree-`p` Čech cohomology refinement diagram with one fixed coefficient presheaf. -/
noncomputable def refinementFunctor
    (F : X.Presheaf AddCommGrpCat.{max u v w}) (p : ℕ) :
    OpenCover.RefinementCategory.{v} X ⥤ AddCommGrpCat.{max u v w} :=
  refinementDiagram X p ⋙ (evaluation _ _).obj F

/-- The fixed-coefficient refinement functor evaluates at a represented cover to its Čech
cohomology. -/
@[simp]
theorem refinementFunctor_obj
    (F : X.Presheaf AddCommGrpCat.{max u v w}) (p : ℕ) (𝒰 : OpenCover.{v} X) :
    (refinementFunctor F p).obj 𝒰.refinementObject = cohomology 𝒰 F p := sorry

/-- On a represented selected refinement, the fixed-coefficient quotient functor uses the
canonical map on Čech cohomology. -/
@[simp]
theorem refinementFunctor_map
    (F : X.Presheaf AddCommGrpCat.{max u v w}) (p : ℕ)
    {𝒰 𝒱 : OpenCover.{v} X} (r : OpenCover.Refinement 𝒰 𝒱) :
    (refinementFunctor F p).map (OpenCover.refinementMap r) =
      cohomologyMap r F p := sorry

end TopCat.Presheaf.Cech


