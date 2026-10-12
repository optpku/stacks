/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Proposition_75_29_4_BoundednessDetection
public import stacks_project.Chap75.Lemma_75_5_6_Tensor

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed (ihomOf adjunctionOf)
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory DerivedCategory.TStructure
open _root_.DerivedCategory CategoryTheory.BraidedCategory
open scoped DerivedExt DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]

/-- A closed owner whose fixed-right tensor functors are identified with geometric derived
tensor supplies the actual derived tensor/internal-Hom adjunction. Its right adjoint is
independent, up to the canonical `Adjunction.rightAdjointUniq`, of the compatible owner. -/
noncomputable def derivedTensorInternalHomAdjunction
    (H : MonoidalClosed (ModuleDerived X))
    (tensorComparison : ∀ P : ModuleDerived X,
      MonoidalCategory.tensorRight P ≅ DerivedTensor.Right.functor P) (P : ModuleDerived X) :
    DerivedTensor.Right.functor P ⊣ ihomOf H P :=
  (adjunctionOf H P).ofNatIsoLeft
    (tensorLeftIsoTensorRight P ≪≫ tensorComparison P)

/-- The derived internal-Hom adjunction represents morphisms from geometric derived tensor,
via the specified natural comparison and the closed owner's tensor adjunction. -/
theorem derivedTensorInternalHomAdjunction_homEquiv_apply
    (H : MonoidalClosed (ModuleDerived X))
    (tensorComparison : ∀ P : ModuleDerived X,
      MonoidalCategory.tensorRight P ≅ DerivedTensor.Right.functor P)
    (P K L : ModuleDerived X) (morphism : K ⊗ᴸ P ⟶ L) :
    (derivedTensorInternalHomAdjunction H tensorComparison P).homEquiv K L morphism =
      (adjunctionOf H P).homEquiv K L
        ((tensorLeftIsoTensorRight P ≪≫ tensorComparison P).hom.app K ≫ morphism) := sorry

/-- The structure-sheaf dual is internal Hom into the canonical module tensor unit,
the structure sheaf, concentrated in degree zero. -/
noncomputable abbrev structureSheafDual
    (H : MonoidalClosed (ModuleDerived X)) (P : ModuleDerived X) : ModuleDerived X :=
  (ihomOf H P).obj ((singleFunctor X.Modules 0).obj (𝟙_ X.Modules))

/-- The structure-sheaf dual evaluates internal Hom at the degree-zero structure sheaf. -/
theorem structureSheafDual_eq
    (H : MonoidalClosed (ModuleDerived X)) (P : ModuleDerived X) :
    structureSheafDual H P =
      (ihomOf H P).obj ((singleFunctor X.Modules 0).obj (𝟙_ X.Modules)) := sorry

/-- A unit comparison identifies the structure-sheaf dual with the closed owner's dual. -/
noncomputable def structureSheafDualUnitIso
    (H : MonoidalClosed (ModuleDerived X))
    (unitComparison : 𝟙_ (ModuleDerived X) ≅
      (singleFunctor X.Modules 0).obj (𝟙_ X.Modules)) (P : ModuleDerived X) :
    (ihomOf H P).obj (𝟙_ (ModuleDerived X)) ≅ structureSheafDual H P :=
  (ihomOf H P).mapIso unitComparison

/-- The dual comparison applies internal Hom to the structure-sheaf unit comparison. -/
theorem structureSheafDualUnitIso_hom
    (H : MonoidalClosed (ModuleDerived X))
    (unitComparison : 𝟙_ (ModuleDerived X) ≅
      (singleFunctor X.Modules 0).obj (𝟙_ X.Modules)) (P : ModuleDerived X) :
    (structureSheafDualUnitIso H unitComparison P).hom =
      (ihomOf H P).map unitComparison.hom := sorry

/-- Structure-sheaf duals are canonically independent of the chosen compatible closed owner. -/
noncomputable def structureSheafDualIso
    (H H' : MonoidalClosed (ModuleDerived X))
    (tensorComparison : ∀ P : ModuleDerived X,
      MonoidalCategory.tensorRight P ≅ DerivedTensor.Right.functor P)
    (tensorComparison' : ∀ P : ModuleDerived X,
      MonoidalCategory.tensorRight P ≅ DerivedTensor.Right.functor P) (P : ModuleDerived X) :
    structureSheafDual H P ≅ structureSheafDual H' P :=
  ((derivedTensorInternalHomAdjunction H tensorComparison P).rightAdjointUniq
    (derivedTensorInternalHomAdjunction H' tensorComparison' P)).app
      ((singleFunctor X.Modules 0).obj (𝟙_ X.Modules))

/-- The dual independence map is the right-adjoint uniqueness map at the structure sheaf. -/
theorem structureSheafDualIso_hom
    (H H' : MonoidalClosed (ModuleDerived X))
    (tensorComparison : ∀ P : ModuleDerived X,
      MonoidalCategory.tensorRight P ≅ DerivedTensor.Right.functor P)
    (tensorComparison' : ∀ P : ModuleDerived X,
      MonoidalCategory.tensorRight P ≅ DerivedTensor.Right.functor P) (P : ModuleDerived X) :
    (structureSheafDualIso H H' tensorComparison tensorComparison' P).hom =
      ((derivedTensorInternalHomAdjunction H tensorComparison P).rightAdjointUniq
        (derivedTensorInternalHomAdjunction H' tensorComparison' P)).hom.app
          ((singleFunctor X.Modules 0).obj (𝟙_ X.Modules)) := sorry

/-- Proposition 75.29.4: for a quasi-compact quasi-separated algebraic space `X` over a
scheme `S`, a perfect weak generator `G` of `D_QCoh(𝒪_X)`, and `E` in `D_QCoh(𝒪_X)`,
bounded-below membership is equivalent to the source's shifted-Hom, Ext, derived-global-Hom,
dual-tensor cohomology, derived-global-sections, and all-perfect-object criteria. The selected
closed owner is identified with geometric derived tensor and the degree-zero structure sheaf;
all tensor expressions below use the actual fixed-right derived tensor construction. -/
@[stacks 0GFI]
theorem boundedBelow_derivedTensor_tfae
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (H : MonoidalClosed (ModuleDerived X))
    (tensorComparison : ∀ P : ModuleDerived X,
      MonoidalCategory.tensorRight P ≅ DerivedTensor.Right.functor P)
    (G E : DerivedQCoh X) (hG_perfect : ModuleDerived.IsPerfect G.obj)
    (hG_generator : IsWeakGenerator G) :
    List.TFAE
      [ (t.plus : ObjectProperty (ModuleDerived X)) E.obj
      , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (G.obj⟦-i⟧ ⟶ E.obj)
      , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(G.obj, E.obj))
      , (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj ((ihomOf H G.obj).obj E.obj))
      , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
          IsZero (cohomologyAb X (structureSheafDual H G.obj ⊗ᴸ E.obj) i)
      , (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj (structureSheafDual H G.obj ⊗ᴸ E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (P⟦-i⟧ ⟶ E.obj)
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(P, E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((moduleDerivedGlobalSectionsAb X).obj ((ihomOf H P).obj E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → IsZero (cohomologyAb X (P ⊗ᴸ E.obj) i)
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((moduleDerivedGlobalSectionsAb X).obj (P ⊗ᴸ E.obj))
      ] := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
