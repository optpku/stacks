/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Differentials.Composition
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transitivity for relative differentials on ringed spaces

For composable morphisms X ⟶ Y ⟶ S, the canonical comparison morphisms form the right-exact
transitivity sequence

  f^* Ω[Y/S] ⟶ Ω[X/S] ⟶ Ω[X/Y] ⟶ 0.

The maps and short complex are explicit data; exactness and epimorphy are exposed separately.
-/

@[expose] public section

open CategoryTheory Limits TopCat TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity

variable {X Y S : RingedSpace.{u}}

/-- The commutative square defining the base-change map in the transitivity sequence. -/
theorem baseChangeSquare (f : X ⟶ Y) (g : Y ⟶ S) :
    CommSq f (f ≫ g) g (𝟙 S) := sorry

/-- The canonical map f^* Ω[Y/S] ⟶ Ω[X/S] in the transitivity sequence. -/
@[stacks 0H79 "base-change transitivity morphism"]
noncomputable def baseChange (f : X ⟶ Y) (g : Y ⟶ S) :
    (RingedSpace.Hom.pullback f).obj Ω[g] ⟶ Ω[f ≫ g] :=
  Differentials.comparison (baseChangeSquare f g)

/-- The left transitivity morphism is the differential comparison attached to the canonical
base-change square. -/
@[stacks 0H79 "base-change transitivity characterization"]
theorem baseChange_isComparison (f : X ⟶ Y) (g : Y ⟶ S) :
    Differentials.IsComparison (baseChange f g) := sorry

/-- The adjoint of the left transitivity morphism sends the universal differential over `S` to
the differential of the pulled section on `X`. -/
@[simp, stacks 0H79 "base-change transitivity on universal differentials"]
theorem baseChange_d
    (f : X ⟶ Y) (g : Y ⟶ S) {U : (Opens Y)ᵒᵖ}
    (t : Y.presheaf.obj U) :
    ((RingedSpace.Hom.pullbackPushforwardAdjunction f).homEquiv _ _
        (baseChange f g)).val.app U ((d[g]).d t) =
      (d[f ≫ g]).d ((RingedSpace.Hom.toRingCatSheafHom f).hom.app U t) := sorry

/-- A morphism with the differential-comparison characterization is the canonical left
transitivity morphism. -/
@[stacks 0H79 "uniqueness of the base-change transitivity morphism"]
theorem eq_baseChange (f : X ⟶ Y) (g : Y ⟶ S)
    {tau : (RingedSpace.Hom.pullback f).obj Ω[g] ⟶ Ω[f ≫ g]}
    (h_tau : Differentials.IsComparison tau) :
    tau = baseChange f g := sorry

/-- The differential-comparison characterization uniquely determines the left transitivity
morphism. -/
@[stacks 0H79 "unique base-change transitivity morphism"]
theorem existsUnique_baseChange (f : X ⟶ Y) (g : Y ⟶ S) :
    ∃! tau : (RingedSpace.Hom.pullback f).obj Ω[g] ⟶ Ω[f ≫ g],
      Differentials.IsComparison tau := sorry

/-- The universal Y-relative differential vanishes on sections pulled back from S. -/
theorem projectionDerivation_base
    (f : X ⟶ Y) (g : Y ⟶ S) {U : (Opens X)ᵒᵖ}
    (a : ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).hom.base).obj
      S.sheaf).obj.obj U) :
    (d[f]).d
      ((RingedSpace.Hom.inverseImageStructureSheafHomComm (f ≫ g)).hom.app U a) = 0 := sorry

/-- The universal Y-relative differential, regarded as an S-relative derivation. -/
@[stacks 0H79 "transitivity projection derivation"]
noncomputable def projectionDerivation (f : X ⟶ Y) (g : Y ⟶ S) :
    RingedSpace.Hom.derivations (f ≫ g) Ω[f] where
  d := (d[f]).d
  d_mul := (d[f]).d_mul
  d_map := (d[f]).d_map
  d_app := projectionDerivation_base f g

/-- Evaluation formula for the derivation inducing the transitivity projection. -/
theorem projectionDerivation_d
    (f : X ⟶ Y) (g : Y ⟶ S) {U : (Opens X)ᵒᵖ}
    (t : X.presheaf.obj U) :
    (projectionDerivation f g).d t = (d[f]).d t := sorry

/-- The canonical map Ω[X/S] ⟶ Ω[X/Y] in the transitivity sequence. -/
@[stacks 0H79 "transitivity projection"]
noncomputable def projection (f : X ⟶ Y) (g : Y ⟶ S) :
    Ω[f ≫ g] ⟶ Ω[f] :=
  RingedSpace.Hom.differentialDesc (f ≫ g) (projectionDerivation f g)

/-- A morphism is the right transitivity morphism when it sends every universal S-relative
differential to the corresponding Y-relative differential. -/
def IsProjection (f : X ⟶ Y) (g : Y ⟶ S)
    (tau : Ω[f ≫ g] ⟶ Ω[f]) : Prop :=
  ∀ {U : (Opens X)ᵒᵖ} (t : X.presheaf.obj U),
    tau.val.app U ((d[f ≫ g]).d t) = (d[f]).d t

/-- The two canonical transitivity morphisms compose to zero. -/
theorem baseChange_comp_projection (f : X ⟶ Y) (g : Y ⟶ S) :
    baseChange f g ≫ projection f g = 0 := sorry

/-- The canonical transitivity short complex for relative differentials of composable
morphisms of ringed spaces. -/
@[stacks 0H79 "transitivity short complex"]
noncomputable def complex (f : X ⟶ Y) (g : Y ⟶ S) :
    ShortComplex (RingedSpace.Modules X) :=
  ShortComplex.mk (baseChange f g) (projection f g)
    (baseChange_comp_projection f g)

/-- The transitivity projection sends the universal differential over S to the universal
differential over Y. -/
@[simp]
theorem projection_d
    (f : X ⟶ Y) (g : Y ⟶ S) {U : (TopologicalSpace.Opens X)ᵒᵖ}
    (t : X.presheaf.obj U) :
    (projection f g).val.app U ((d[f ≫ g]).d t) =
      (d[f]).d t := sorry

/-- The canonical transitivity projection satisfies its generator characterization. -/
theorem projection_isProjection (f : X ⟶ Y) (g : Y ⟶ S) :
    IsProjection f g (projection f g) := sorry

/-- A morphism with the generator characterization is the canonical transitivity
morphism. -/
theorem eq_projection (f : X ⟶ Y) (g : Y ⟶ S)
    {tau : Ω[f ≫ g] ⟶ Ω[f]} (h_tau : IsProjection f g tau) :
    tau = projection f g := sorry

/-- The generator characterization uniquely determines the transitivity projection. -/
theorem existsUnique_projection (f : X ⟶ Y) (g : Y ⟶ S) :
    ∃! tau : Ω[f ≫ g] ⟶ Ω[f], IsProjection f g tau := sorry

/-- The canonical transitivity short complex for relative differentials of composable
morphisms of ringed spaces is exact. -/
@[stacks 0H79]
theorem exact (f : X ⟶ Y) (g : Y ⟶ S) :
    (complex f g).Exact := sorry

/-- The projection in the transitivity sequence for relative differentials is an epimorphism. -/
@[stacks 0H79 "transitivity projection epimorphism"]
instance projection_epi (f : X ⟶ Y) (g : Y ⟶ S) :
    Epi (projection f g) := sorry

/-- The canonical transitivity sequence for relative differentials is exact through its
terminal zero object. -/
theorem exact_and_epi (f : X ⟶ Y) (g : Y ⟶ S) :
    (complex f g).Exact ∧ Epi (projection f g) := sorry

end AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity
