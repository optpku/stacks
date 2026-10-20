module

public import ReasLib.Algebra.Category.ModuleCat.SymmetricPower
public import ReasLib.LinearAlgebra.TensorPower.Symmetric.Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# First symmetric powers in `ModuleCat`

The one-input symmetric tensor power is canonically the original module.  Both
orientations are exposed: `iso₁` follows the Mathlib convention, while
`degreeOneIso` points from a module to its first symmetric power.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u v

namespace ModuleCat.symmetricPower

variable {R : Type u} [CommRing R]

/-- The one-input identity multilinear map is invariant under permutations. -/
theorem degreeOne_invariant (M : ModuleCat.{max u v} R) :
    SymmetricPower.IsInvariant
      (MultilinearMap.ofSubsingleton R M M
        (0 : SymmetricPower.UFin 1) LinearMap.id) := sorry

/-- Evaluation of a first symmetric tensor at its unique input. -/
@[stacks 01CF "first symmetric power evaluation"]
noncomputable def degreeOneInv (M : ModuleCat.{max u v} R) :
    M.symmetricPower 1 ⟶ M :=
  ModuleCat.ofHom
    (SymmetricPower.lift
      (MultilinearMap.ofSubsingleton R M M
        (0 : SymmetricPower.UFin 1) LinearMap.id)
      (degreeOne_invariant M))

/-- The canonical map from a module to its first symmetric power. -/
@[stacks 01CF "module as its first symmetric power"]
noncomputable def degreeOne (M : ModuleCat.{max u v} R) :
    M ⟶ M.symmetricPower 1 :=
  ModuleCat.ofHom
    ((MultilinearMap.ofSubsingleton R M (M.symmetricPower 1)
        (0 : SymmetricPower.UFin 1)).symm
      (ModuleCat.symmetricPower.mk (M := M) (n := 1)))

/-- The forward first-symmetric-power map followed by evaluation is the identity. -/
theorem degreeOne_hom_inv_id (M : ModuleCat.{max u v} R) :
    degreeOne M ≫ degreeOneInv M = 𝟙 _ := sorry

/-- Evaluation followed by the first-symmetric-power map is the identity. -/
theorem degreeOne_inv_hom_id (M : ModuleCat.{max u v} R) :
    degreeOneInv M ≫ degreeOne M = 𝟙 _ := sorry

/-- The canonical Mathlib-oriented isomorphism from the first symmetric power to the module. -/
@[stacks 01CF "first symmetric power isomorphism"]
noncomputable def iso₁ (M : ModuleCat.{max u v} R) :
    M.symmetricPower 1 ≅ M :=
  { hom := degreeOneInv M
    inv := degreeOne M
    hom_inv_id := degreeOne_inv_hom_id M
    inv_hom_id := degreeOne_hom_inv_id M }

/-- The canonical first symmetric-power isomorphism evaluates on its unique input. -/
@[simp]
theorem iso₁_hom_apply {M : ModuleCat.{max u v} R}
    (m : SymmetricPower.UFin 1 → M) :
    (iso₁ M).hom (ModuleCat.symmetricPower.mk m) = m 0 := sorry

/-- The canonical isomorphism from a module to its first symmetric power. -/
@[stacks 01CF "module as its first symmetric power identification"]
noncomputable def degreeOneIso (M : ModuleCat.{max u v} R) :
    M ≅ M.symmetricPower 1 :=
  (iso₁ M).symm

/-- The forward map of `degreeOneIso` is `degreeOne`. -/
@[simp]
theorem degreeOneIso_hom (M : ModuleCat.{max u v} R) :
    (degreeOneIso M).hom = degreeOne M := sorry

/-- The inverse map of `degreeOneIso` is evaluation. -/
@[simp]
theorem degreeOneIso_inv (M : ModuleCat.{max u v} R) :
    (degreeOneIso M).inv = degreeOneInv M := sorry

/-- Evaluation of the inverse first-symmetric-power isomorphism on a generator. -/
@[simp]
theorem degreeOneIso_inv_apply {M : ModuleCat.{max u v} R}
    (m : SymmetricPower.UFin 1 → M) :
    (degreeOneIso M).inv (ModuleCat.symmetricPower.mk m) = m 0 := sorry

/-- The first symmetric-power map is an isomorphism. -/
instance degreeOne_isIso (M : ModuleCat.{max u v} R) :
    IsIso (degreeOne M) := sorry

/-- First symmetric-power maps are natural in the module. -/
@[reassoc]
theorem degreeOne_naturality
    {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    f ≫ degreeOne N = degreeOne M ≫ ModuleCat.symmetricPower.map f 1 := sorry

/-- Naturality of the inverse first-symmetric-power maps. -/
theorem degreeOneIso_inv_naturality
    {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    ModuleCat.symmetricPower.map f 1 ≫ (degreeOneIso N).inv =
      (degreeOneIso M).inv ≫ f := sorry

/-- The canonical `Sym¹` evaluation is natural in the module. -/
theorem iso₁_hom_naturality
    {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    ModuleCat.symmetricPower.map f 1 ≫ (iso₁ N).hom =
      (iso₁ M).hom ≫ f := sorry

/-- The degree-one maps form the forward natural transformation. -/
@[stacks 01CF "forward first symmetric power natural transformation"]
noncomputable def degreeOneNatTrans :
    (𝟭 (ModuleCat.{max u v} R)) ⟶
      ModuleCat.symmetricPower.functor R 1 where
  app M := degreeOne M
  naturality _ _ f := degreeOne_naturality f

/-- The inverse degree-one maps form the reverse natural transformation. -/
@[stacks 01CF "inverse first symmetric power natural transformation"]
noncomputable def degreeOneInvNatTrans :
    ModuleCat.symmetricPower.functor R 1 ⟶
      (𝟭 (ModuleCat.{max u v} R)) where
  app M := (degreeOneIso M).inv
  naturality _ _ f := degreeOneIso_inv_naturality f

/-- The forward degree-one natural transformation followed by its inverse is the identity. -/
@[simp]
theorem degreeOneNatTrans_hom_inv_id :
    degreeOneNatTrans (R := R) ≫ degreeOneInvNatTrans (R := R) = 𝟙 _ := sorry

/-- The inverse degree-one natural transformation followed by the forward one is the identity. -/
@[simp]
theorem degreeOneNatTrans_inv_hom_id :
    degreeOneInvNatTrans (R := R) ≫ degreeOneNatTrans (R := R) = 𝟙 _ := sorry

/-- Modules are naturally isomorphic to their first symmetric powers. -/
@[stacks 01CF "natural first symmetric power"]
noncomputable def degreeOneNatIso :
    (𝟭 (ModuleCat.{max u v} R)) ≅
      ModuleCat.symmetricPower.functor R 1 :=
  { hom := degreeOneNatTrans (R := R)
    inv := degreeOneInvNatTrans (R := R)
    hom_inv_id := degreeOneNatTrans_hom_inv_id (R := R)
    inv_hom_id := degreeOneNatTrans_inv_hom_id (R := R) }

/-- A component of `degreeOneNatIso` is `degreeOneIso`. -/
@[simp]
theorem degreeOneNatIso_app (M : ModuleCat.{max u v} R) :
    (degreeOneNatIso (R := R)).app M = degreeOneIso M := sorry

/-- The forward map of `degreeOneNatIso` is explicit. -/
@[simp]
theorem degreeOneNatIso_hom :
    (degreeOneNatIso (R := R)).hom = degreeOneNatTrans (R := R) := sorry

/-- The inverse map of `degreeOneNatIso` is explicit. -/
@[simp]
theorem degreeOneNatIso_inv :
    (degreeOneNatIso (R := R)).inv = degreeOneInvNatTrans (R := R) := sorry

/-- The forward component of `degreeOneNatIso` is `degreeOne`. -/
@[simp]
theorem degreeOneNatIso_hom_app (M : ModuleCat.{max u v} R) :
    (degreeOneNatIso (R := R)).hom.app M = degreeOne M := sorry

/-- The inverse component of `degreeOneNatIso` is evaluation. -/
@[simp]
theorem degreeOneNatIso_inv_app (M : ModuleCat.{max u v} R) :
    (degreeOneNatIso (R := R)).inv.app M = (degreeOneIso M).inv := sorry

end ModuleCat.symmetricPower
