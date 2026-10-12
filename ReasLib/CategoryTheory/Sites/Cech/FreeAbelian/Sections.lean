/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.FreeAbelian.Comparison
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor form of the fixed-target free-abelian Cech complex

The source expression `Z_(family) ⊗_Z O` is modeled by free presheaves of modules over the
underlying ring presheaf.  This is the canonical presheaf-level tensor presentation used by
Mathlib's `PresheafOfModules.free`; it keeps the `O`-module structure instead of reducing to an
evaluation-at-one-object statement.  The older slice-section construction is retained below in a
separate namespace as a useful evaluation companion.
-/

@[expose] public section

noncomputable section

universe u v w

namespace CategoryTheory.Cech.FreeAbelian

open Limits Opposite AlgebraicTopology

variable {C : Type u} [Category.{v} C] {U : C} {ι : Type w}

/-- The underlying ring presheaf of a commutative-ring-valued presheaf. -/
abbrev underlyingRing (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    Cᵒᵖ ⥤ RingCat.{max u v} :=
  𝒪 ⋙ forget₂ CommRingCat RingCat

/-- The free module presheaf represented by an object of `C`, over `underlyingRing 𝒪`. -/
@[stacks 03F5 "free module representable for the tensor presentation"]
noncomputable abbrev freeModuleRepresentable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    C ⥤ PresheafOfModules.{max u v} (underlyingRing 𝒪) :=
  uliftYoneda.{u} ⋙ PresheafOfModules.free (underlyingRing 𝒪)

/-- Lemma 21.9.5 (Tag 03F5): the presheaf-level tensor presentation of the free-abelian
fixed-target Cech complex with coefficients in `𝒪`. -/
@[stacks 03F5 "presheaf-level fixed-target tensor Cech complex"]
noncomputable abbrev tensorCoverComplex (family : ι → Over U)
    [HasIteratedFiberProducts family]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
    [Limits.HasCoproducts.{w} (PresheafOfModules.{max u v} (underlyingRing 𝒪))] :
    ChainComplex (PresheafOfModules.{max u v} (underlyingRing 𝒪)) ℕ :=
  (alternatingFaceMapComplex
      (PresheafOfModules.{max u v} (underlyingRing 𝒪))).obj
    (familyCech family ⋙ FormalCoproduct.forgetOver U ⋙
      (FormalCoproduct.eval.{w} C
        (PresheafOfModules.{max u v} (underlyingRing 𝒪))).obj
        (freeModuleRepresentable 𝒪))

/-- Lemma 21.9.5 (Tag 03F5): the presheaf tensor Cech complex is exact in every positive
successor degree. -/
@[stacks 03F5 "presheaf-level fixed-target tensor Cech homology vanishing"]
theorem tensorCoverComplex_homology_isZero_succ (family : ι → Over U)
    [HasIteratedFiberProducts family]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
    [Limits.HasCoproducts.{w} (PresheafOfModules.{max u v} (underlyingRing 𝒪))] (i : ℕ) :
    IsZero ((tensorCoverComplex family 𝒪).homology (i + 1)) := sorry

/-- Positive-degree view of the presheaf tensor Cech exactness theorem. -/
theorem tensorCoverComplex_homology_isZero_of_pos (family : ι → Over U)
    [HasIteratedFiberProducts family]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
    [Limits.HasCoproducts.{w} (PresheafOfModules.{max u v} (underlyingRing 𝒪))]
    (i : ℕ) (hi : 0 < i) :
    IsZero ((tensorCoverComplex family 𝒪).homology i) := sorry

end CategoryTheory.Cech.FreeAbelian

/-! The following namespace is an evaluation companion for users who explicitly need a slice
object and a scalar extension at that object.  It is not the source-level 03F5 carrier. -/
namespace CategoryTheory.Cech.FreeAbelian.Sectionwise

open Limits Opposite

variable {C : Type u} [Category.{v} C]

/-- The slice evaluation of the fixed-target free-abelian Cech complex in `Z`-modules. -/
abbrev chainComplex {U : C} (family : ι → Over U) [HasIteratedFiberProducts family]
    [HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{v})] [HasProducts AddCommGrpCat.{v}]
    (V : Over U) : ChainComplex (ModuleCat.{v} ℤ) ℕ :=
  ((((evaluation (Over U)ᵒᵖ AddCommGrpCat.{v}).obj (op V)) ⋙
      (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).asEquivalence.inverse).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (freeAbelianCechChainComplex family)

/-- The slice sectionwise scalar-extension companion for a commutative-ring presheaf. -/
abbrev tensorChainComplex {U : C} (𝒪 : Cᵒᵖ ⥤ CommRingCat.{v})
    (family : ι → Over U) [HasIteratedFiberProducts family]
    [HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{v})] [HasProducts AddCommGrpCat.{v}]
    (V : Over U) : ChainComplex (ModuleCat.{v} (((Over.forget U).op ⋙ 𝒪).obj (op V))) ℕ :=
  ((ModuleCat.extendScalars
      (Int.castRingHom (((Over.forget U).op ⋙ 𝒪).obj (op V)))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (chainComplex family V)

/-- Sectionwise scalar extension of the slice companion has vanishing positive homology. -/
theorem tensorChainComplex_homology_isZero_succ {U : C}
    (family : ι → Over U) [HasIteratedFiberProducts family]
    [HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{v})] [HasProducts AddCommGrpCat.{v}]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{v}) (V : Over U) (i : ℕ) :
    IsZero ((tensorChainComplex 𝒪 family V).homology (i + 1)) := sorry

end CategoryTheory.Cech.FreeAbelian.Sectionwise

end
