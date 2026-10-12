/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Derivation.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension.Module
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.GlobalSections
public import ReasLib.CategoryTheory.Sites.Cohomology.Boundary
public import ReasLib.Topology.Opens.Instances
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0B8S

# Boundary derivations of square-zero extensions

For a locally surjective square-zero extension of commutative-ring sheaves, this leaf constructs
the boundary map as explicit data and records the Leibniz identity separately.  The resulting
derivation uses the canonical target-module descent and makes no choice of a splitting.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Cohomology.SquareZero

variable {X : TopCat.{u}}

variable {A O : X.Sheaf CommRingCat.{u}} {π : A ⟶ O}

/-- A global section of a commutative-ring sheaf, viewed as a global section of its underlying
additive sheaf. -/
@[stacks 0B8S "global section viewed in the additive kernel sequence"]
noncomputable abbrev globalSectionAdditive (π : A ⟶ O)
    (r : globalSectionsRing O.toRingedSpace) :
    (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (KernelIdeal.underlyingTarget (J := Opens.grothendieckTopology X) (A := A) (Q := O) π) :=
  (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      (Preorder.isTerminalTop (Opens X))).inv.app
        (KernelIdeal.underlyingTarget (J := Opens.grothendieckTopology X) (A := A) (Q := O) π)
    r

/-- The additive global-section comparison preserves zero. -/
theorem globalSectionAdditive_zero (π : A ⟶ O) :
    globalSectionAdditive π 0 = 0 := sorry

/-- The additive global-section comparison preserves addition. -/
theorem globalSectionAdditive_add (π : A ⟶ O)
    (r s : globalSectionsRing O.toRingedSpace) :
    globalSectionAdditive π (r + s) =
      globalSectionAdditive π r + globalSectionAdditive π s := sorry

/-- The additive homomorphism from ring-valued global sections to additive global sections. -/
@[stacks 0B8S "global-section additive comparison"]
noncomputable def globalSectionsAddHom (π : A ⟶ O) :
    globalSectionsRing O.toRingedSpace →+
      (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (KernelIdeal.underlyingTarget (J := Opens.grothendieckTopology X) (A := A) (Q := O) π) where
  toFun := globalSectionAdditive π
  map_zero' := globalSectionAdditive_zero π
  map_add' := globalSectionAdditive_add π

variable [Sheaf.IsLocallySurjective π]

/-- The kernel coefficient sheaf, descended canonically to an `O`-module. -/
@[stacks 0B8S "coefficient module of a square-zero boundary derivation"]
noncomputable abbrev coefficient (hzero : KernelIdeal.IsSquareZero π) :
    O.toRingedSpace.Modules :=
  hzero.targetModule (inferInstance : IsIso (KernelIdeal.quotientComparison π))

/-- The degree-one cohomology module in which the square-zero boundary derivation takes values. -/
@[stacks 0B8S "target of a square-zero boundary derivation"]
abbrev H1 (hzero : KernelIdeal.IsSquareZero π) :=
  Sheaf.H ((moduleUnderlyingSheaf O.toRingedSpace).obj (coefficient hzero)) 1

/-- The first cohomology of the descended coefficient module is the first cohomology of the
underlying kernel ideal. -/
@[stacks 0B8S "canonical cohomology equivalence for the square-zero kernel"]
noncomputable def H1_kernelEquiv (hzero : KernelIdeal.IsSquareZero π) :
    H1 hzero ≃+ ((KernelIdeal.underlyingShortComplex π).X₁).H 1 :=
by
  let e := hzero.targetModuleForgetIso
    (inferInstance : IsIso (KernelIdeal.quotientComparison π))
  exact
    { toFun := Sheaf.H.map e.hom 1
      invFun := Sheaf.H.map e.inv 1
      left_inv := fun x ↦ by
        rw [← Sheaf.H.map_comp_apply, e.hom_inv_id]
        exact Sheaf.H.map_id_apply x
      right_inv := fun x ↦ by
        rw [← Sheaf.H.map_comp_apply, e.inv_hom_id]
        exact Sheaf.H.map_id_apply x
      map_add' := (Sheaf.H.map e.hom 1).map_add }

/-- The first cohomology of the descended coefficient module is the first cohomology of the
underlying kernel ideal. -/
@[stacks 0B8S "cohomology comparison for the square-zero kernel"]
theorem H1_isomorphic_kernel (hzero : KernelIdeal.IsSquareZero π) :
    IsIsomorphic (H1 hzero)
      (((KernelIdeal.underlyingShortComplex π).X₁).H 1) := sorry

/-- Typeclass bridge for the abbreviated `H1` carrier.  The generic global cohomology instance
cannot unfold the square-zero coefficient abbreviation while elaborating scalar expressions. -/
@[stacks 0B8S "module structure on square-zero coefficient cohomology"]
noncomputable instance h1Module (hzero : KernelIdeal.IsSquareZero π) :
    Module (globalSectionsRing O.toRingedSpace) (H1 hzero) :=
  AlgebraicGeometry.RingedSpace.Module.Cohomology.globalModule
    (X := O.toRingedSpace) (coefficient hzero) 1

/-- The boundary map of the underlying additive short exact sequence, transported to the
canonically descended kernel coefficient module. -/
@[stacks 0B8S "linear map underlying a square-zero boundary derivation"]
noncomputable def boundaryLinearMap (hzero : KernelIdeal.IsSquareZero π) :
    globalSectionsRing O.toRingedSpace →ₗ[ℤ] H1 hzero :=
  ((Sheaf.H.map
      (hzero.targetModuleForgetIso
        (inferInstance : IsIso (KernelIdeal.quotientComparison π))).inv 1).comp
    (((KernelIdeal.underlyingShortComplex_shortExact π).globalBoundary).toAddMonoidHom.comp
      (globalSectionsAddHom π))).toIntLinearMap

/-- The square-zero boundary map satisfies the Leibniz identity for the canonical global-section
action on its target cohomology. -/
@[stacks 0B8S "Leibniz identity for the square-zero boundary map"]
theorem boundaryLinearMap_leibniz (hzero : KernelIdeal.IsSquareZero π)
    (r s : globalSectionsRing O.toRingedSpace) :
    boundaryLinearMap hzero (r * s) =
      r • boundaryLinearMap hzero s + s • boundaryLinearMap hzero r := sorry

/-- Lemma 20.25.5 (0B8S): the connecting map of a locally surjective square-zero extension is
the canonical derivation from global functions to first cohomology of its kernel. -/
@[stacks 0B8S "square-zero boundary derivation"]
noncomputable def boundaryDerivation (hzero : KernelIdeal.IsSquareZero π) :
    Derivation ℤ (globalSectionsRing O.toRingedSpace) (H1 hzero) :=
  Derivation.mk' (boundaryLinearMap hzero) (boundaryLinearMap_leibniz hzero)

/-- The linear map underlying `boundaryDerivation hzero` is the explicit boundary map. -/
@[stacks 0B8S "underlying map of the square-zero boundary derivation"]
theorem boundaryDerivation_toLinearMap (hzero : KernelIdeal.IsSquareZero π) :
    (boundaryDerivation hzero).toLinearMap = boundaryLinearMap hzero := sorry

end AlgebraicGeometry.RingedSpace.Module.Cohomology.SquareZero
