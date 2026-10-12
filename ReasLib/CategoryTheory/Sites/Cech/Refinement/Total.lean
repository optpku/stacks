/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Presheaf.Cech.Total
public import ReasLib.Topology.Opens.Instances
public import ReasLib.CategoryTheory.Sites.Cech.Refinement
import Mathlib.Tactic.CrossRefAttribute

/-!
# Total Čech refinement

@stack 08BM

This leaf lifts the coefficient-free indexed-open refinement map through the row, double, and
total Čech functors.  The morphism at each layer is concrete; only the final projection formula
is a deferred propositional companion.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace ComplexShape HomologicalComplex₂
open CategoryTheory.Limits
open AlgebraicTopology
open TopCat.Presheaf.Cech.Total

noncomputable section

universe u v

namespace CategoryTheory.Cech.Refinement

variable {X : TopCat.{u}} {I J : Type v}

/-- The row Čech refinement natural transformation induced by an indexed-open refinement. -/
@[stacks 08BM "row Cech refinement"]
noncomputable abbrev row
    (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I) (ht : IsRefinement 𝒰 𝒱 t) :
    rowCechFunctor 𝒰 ⟶ rowCechFunctor 𝒱 :=
  Functor.whiskerRight (cechRefinementNatTrans 𝒰 𝒱 t ht)
    (embeddingUpNat.extendFunctor AddCommGrpCat.{max u v})

/-- The double Čech refinement natural transformation induced by an indexed-open refinement. -/
@[stacks 08BM "double Cech refinement"]
noncomputable abbrev double
    (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I) (ht : IsRefinement 𝒰 𝒱 t) :
    doubleCechFunctor 𝒰 ⟶ doubleCechFunctor 𝒱 :=
  NatTrans.mapHomologicalComplex (row 𝒰 𝒱 t ht) (up ℤ)

/-- The total Čech refinement natural transformation induced by an indexed-open refinement. -/
@[stacks 08BM "total Cech refinement"]
noncomputable abbrev total
    (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I) (ht : IsRefinement 𝒰 𝒱 t) :
    totalCechFunctor 𝒰 ⟶ totalCechFunctor 𝒱 :=
  Functor.whiskerRight (double 𝒰 𝒱 t ht)
    (totalFunctor AddCommGrpCat.{max u v} (up ℤ) (up ℤ) (up ℤ))

/-- The total Čech complex map associated to a refinement, evaluated at a coefficient complex. -/
@[stacks 08BM "total Cech refinement map"]
noncomputable def map (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I)
    (ht : IsRefinement 𝒰 𝒱 t)
    (F : CochainComplex (X.Presheaf AddCommGrpCat.{max u v}) ℤ) :
    (totalCechFunctor 𝒰).obj F ⟶ (totalCechFunctor 𝒱).obj F :=
  (total 𝒰 𝒱 t ht).app F

/-- The total Čech refinement map is the totalization of its double-complex refinement map. -/
@[stacks 08BM "total Cech refinement map as a totalized double map", simp]
theorem map_eq_total_map (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I)
    (ht : IsRefinement 𝒰 𝒱 t)
    (F : CochainComplex (X.Presheaf AddCommGrpCat.{max u v}) ℤ) :
    map 𝒰 𝒱 t ht F =
      HomologicalComplex₂.total.map ((double 𝒰 𝒱 t ht).app F) (up ℤ) := sorry

/-- The total Čech refinement map is natural in the coefficient complex. -/
@[reassoc, stacks 08BM "naturality of the total Cech refinement map"]
theorem map_naturality (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I)
    (ht : IsRefinement 𝒰 𝒱 t)
    {F G : CochainComplex (X.Presheaf AddCommGrpCat.{max u v}) ℤ} (f : F ⟶ G) :
    (totalCechFunctor 𝒰).map f ≫ map 𝒰 𝒱 t ht G =
      map 𝒰 𝒱 t ht F ≫ (totalCechFunctor 𝒱).map f := sorry

end CategoryTheory.Cech.Refinement

end
