/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.AffineEvaluation
public import ReasLib.AlgebraicTopology.Cech.Nerve.Coefficients
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison
public import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

namespace SheafOfModules.IsAdequate

variable {S : Scheme.{u}} {τ : StandardTopology}

/-- For an affine flat surjective arrow, an adequate module sheaf has an acyclic
extended coefficient-valued Cech complex. -/
@[stacks 06VL]
theorem extendedCech_acyclic
    {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)}
    (hℱ : IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
      affineEvaluationUnderlying ℱ)
    (U V : Over S) (g : V ⟶ U) [IsAffine U.left] [IsAffine V.left]
    [Flat g.left] [Surjective g.left] :
    (Arrow.Cech.extended (A := AddCommGrpCat) (Arrow.mk g) ℱ.val.presheaf).Acyclic := sorry

/-- An adequate module sheaf satisfies the sheaf condition for the fpqc topology. -/
@[stacks 06VL]
theorem isSheaf_fpqc
    {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)}
    (hℱ : IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
      affineEvaluationUnderlying ℱ) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) ℱ.val.presheaf := sorry

/-- An adequate module sheaf satisfies the sheaf condition for the fppf topology. -/
@[stacks 06VL]
theorem isSheaf_fppf
    {ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)}
    (hℱ : IsAdequate ModuleValuedFunctor.tensorExtensionUnderlying
      affineEvaluationUnderlying ℱ) :
    Presheaf.IsSheaf (StandardTopology.fppf.overTopology S) ℱ.val.presheaf := sorry

end SheafOfModules.IsAdequate
