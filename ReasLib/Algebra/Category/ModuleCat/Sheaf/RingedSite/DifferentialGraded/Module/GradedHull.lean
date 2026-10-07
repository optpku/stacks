module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.GradedModule.Shift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Limits
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.Tactic.CrossRefAttribute

/-!
# The differential graded hull of a graded module

The forgetful functor from differential graded modules to graded modules has a left adjoint.
This leaf owns that adjoint and the full graded-module morphism from a graded module to the shift
of the cokernel of the adjunction unit.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule
open scoped DifferentialGradedAlgebra.GradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}}

/-- A differential graded hull is a specified left adjoint to the functor forgetting the
differential.  Keeping the functor explicit prevents proof-only adjoint existence from selecting
public data. -/
@[stacks 0FSK "differential graded hull"]
structure GradedHull (A : DGA(O)) where
  /-- The functor adjoining a differential to a graded module. -/
  toFunctor : DifferentialGradedAlgebra.GradedModule A ⥤ Mod(A, d)
  /-- The defining adjunction of a differential graded hull. -/
  adjunction : toFunctor ⊣ forgetToGraded A

/-- Lemma 24.24.1 (0FSK): a differential graded hull exists. -/
@[stacks 0FSK "existence of a differential graded hull"]
theorem GradedHull.nonempty (A : DGA(O)) : Nonempty (GradedHull A) := sorry

/-- Lemma 24.24.1 (0FSK), in the canonical Mathlib interface: forgetting the differential is a
right adjoint. -/
@[stacks 0FSK "graded forgetful functor is a right adjoint"]
noncomputable instance forgetToGraded_isRightAdjoint (A : DGA(O)) :
    (forgetToGraded A).IsRightAdjoint := sorry

namespace GradedHull

variable {A : DGA(O)}

/-- Any two specified differential graded hull functors are canonically isomorphic. -/
noncomputable def iso (G H : GradedHull A) : G.toFunctor ≅ H.toFunctor :=
  G.adjunction.leftAdjointUniq H.adjunction

/-- The unit from a graded module to the underlying graded module of its specified differential
graded hull. -/
@[stacks 0FSL "unit of the differential graded hull"]
noncomputable def unit (G : GradedHull A) :
    𝟭 (DifferentialGradedAlgebra.GradedModule A) ⟶
      G.toFunctor ⋙ forgetToGraded A :=
  G.adjunction.unit

/-- The cokernel of the differential graded hull unit at a graded module. -/
@[stacks 0FSL "cokernel of the differential graded hull unit"]
noncomputable def cokernel (G : GradedHull A)
    (N : DifferentialGradedAlgebra.GradedModule A) :
    DifferentialGradedAlgebra.GradedModule A :=
  Limits.cokernel ((G.unit).app N)

/-- The canonical graded `A`-module morphism
`N ⟶ (cokernel (N ⟶ F(G(N))))[1]` induced by the differential on a specified hull. -/
@[stacks 0FSL "bar differential of the differential graded hull"]
noncomputable def barD (G : GradedHull A)
    (N : DifferentialGradedAlgebra.GradedModule A) :
    N ⟶ (G.cokernel N)[1] where
  hom n :=
    ((G.unit).app N).hom n ≫
      (G.toFunctor.obj N).toComplex.d n (n + 1) ≫
        (Limits.cokernel.π ((G.unit).app N)).hom (n + 1)
  comm := sorry

/-- The degree-`n` component of the canonical bar differential is the hull differential followed
by the cokernel projection. -/
@[simp]
theorem barD_hom (G : GradedHull A)
    (N : DifferentialGradedAlgebra.GradedModule A) (n : ℤ) :
    (G.barD N).hom n =
      ((G.unit).app N).hom n ≫
        (G.toFunctor.obj N).toComplex.d n (n + 1) ≫
          (Limits.cokernel.π ((G.unit).app N)).hom (n + 1) := sorry

/-- Lemma 24.24.2 (0FSL) (1): the unit into the underlying graded differential graded hull is
canonically monic. -/
@[stacks 0FSL "(1), the hull unit is monic"]
instance unit_mono (G : GradedHull A)
    (N : DifferentialGradedAlgebra.GradedModule A) :
    Mono ((G.unit).app N) := sorry

/-- Lemma 24.24.2 (0FSL) (2): the canonical bar differential canonically identifies a graded
module with the shift of the cokernel of the hull unit. -/
@[stacks 0FSL "(2), the hull bar differential is an isomorphism"]
instance barD_isIso (G : GradedHull A)
    (N : DifferentialGradedAlgebra.GradedModule A) :
    IsIso (G.barD N) := sorry

/-- Lemma 24.24.2 (0FSL) (3): every specified differential graded hull is acyclic. -/
@[stacks 0FSL "(3), the differential graded hull is acyclic"]
theorem acyclic (G : GradedHull A)
    (N : DifferentialGradedAlgebra.GradedModule A) :
    HomologicalComplex.Acyclic (G.toFunctor.obj N).toComplex := sorry

-- Every datum below takes a specified hull.  Its inherited `sorryAx` occurs only through
-- functoriality, adjunction, and graded-linearity law fields; no datum selects a hull from
-- `GradedHull.nonempty` or from `forgetToGraded_isRightAdjoint`.

end GradedHull

end SheafOfModules.RingedSite.DifferentialGradedModule

end
