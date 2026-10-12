/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_36_1_ChernPower
public import stacks_project.Chap42.Lemma_42_36_3_VectorBundle
public import stacks_project.Chap42.Lemma_42_55_1
public import stacks_project.Chap42.«42_39_1_1_ChernClassTheory»
public import stacks_project.Chap42.Lemma_42_55_2_Compactification
public import stacks_project.Chap42.Lemma_42_55_2_PushPull

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Scheme.ProjectiveBundle.Compactification
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Lemma 42.55.2 (1): for the infinity section in the projective compactification of a
rank-`r` vector bundle, the positive Chern components of its pushed-forward structure sheaf
vanish in every degree strictly below `r`. -/
@[stacks 0FEF]
theorem component_infinityStructureSheaf_eq_zero
    {S X E : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (C : X.Modules) (r : ℕ)
    [hC : C.IsFiniteLocallyFreeOfRank r] (π : E ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules))
    (classes : @ChernClass.Theory S δ inferInstance inferInstance E (π ≫ p)
      (hπ.locallyOfFiniteTypeComp r p)) (t : ℕ) (ht : 0 < t) (htr : t < r) :
    @ChernClass.Theory.component S inferInstance δ inferInstance E (π ≫ p)
        (hπ.locallyOfFiniteTypeComp r p) classes
        (infinityStructureSheaf C π hπ) t = 0 := sorry

/-- Lemma 42.55.2 (2): in the cospan operational Chow group for the vector-bundle inclusion
`j : C ⟶ E`, the operation `p^* ∘ π_*` applied to the top Chern component of the pushed-forward
structure sheaf is `(-1)^(r - 1) * (r - 1)!` times flat pullback along `j`. -/
@[stacks 0FEF]
theorem pushPull_component_infinityStructureSheaf
    {S X E : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (C : X.Modules) (r : ℕ)
    [hC : C.IsFiniteLocallyFreeOfRank r] (π : E ⟶ X)
    (hπ : Scheme.ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules))
    (V : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra C))
    [hV : Scheme.IsRelativeSpectrumOver V]
    (A : AffineChart C V π hπ)
    (classes : @ChernClass.Theory S δ inferInstance inferInstance E (π ≫ p)
      (hπ.locallyOfFiniteTypeComp r p)) :
    @BivariantClass.Cospan.pushPull S inferInstance δ inferInstance
        (Over.mk (Scheme.associatedVectorBundleπ C V ≫ p)) (Over.mk (π ≫ p)) (Over.mk p)
        (@Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp S (Over.mk p) inferInstance C
          (Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank r C) V hV)
        (hπ.locallyOfFiniteTypeComp r p) inferInstance
        (Over.homMk (Scheme.associatedVectorBundleπ C V)) (Over.homMk π) r
        (@Scheme.AssociatedVectorBundle.overHomFlat S (Over.mk p) C
          (Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank r C) V hV)
        (@Scheme.AssociatedVectorBundle.overHomRelativeDimension S (Over.mk p) C r hC V
          hV)
        (hπ.isProperOfFiniteLocallyFree r)
        (@ChernClass.Theory.component S inferInstance δ inferInstance E (π ≫ p)
          (hπ.locallyOfFiniteTypeComp r p) classes
          (infinityStructureSheaf C π hπ) r) =
      @BivariantClass.Cospan.scale S inferInstance δ inferInstance
        (Over.mk (Scheme.associatedVectorBundleπ C V ≫ p)) (Over.mk (π ≫ p)) (Over.mk p)
        (@Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp S (Over.mk p) inferInstance C
          (Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank r C) V hV)
        (hπ.locallyOfFiniteTypeComp r p) inferInstance
        (Over.homMk (Scheme.associatedVectorBundleπ C V)) (Over.homMk π) 0
        (((-1 : ℤ) ^ (r - 1)) * (Nat.factorial (r - 1) : ℤ))
        (@BivariantClass.Cospan.ofOverMorphism S inferInstance δ inferInstance
          (Over.mk (Scheme.associatedVectorBundleπ C V ≫ p)) (Over.mk (π ≫ p)) (Over.mk p)
          (@Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp S (Over.mk p) inferInstance C
            (Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank r C) V hV)
          (hπ.locallyOfFiniteTypeComp r p) inferInstance
          (Over.homMk (Scheme.associatedVectorBundleπ C V)) (Over.homMk π)
          (AffineChart.jOver C V π hπ A p)
          (AffineChart.jOver_projection C V π hπ A p) 0
          (@BivariantClass.flatPullback S inferInstance δ inferInstance
            (Over.mk (Scheme.associatedVectorBundleπ C V ≫ p)) (Over.mk (π ≫ p))
            (@Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp S (Over.mk p) inferInstance C
              (Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank r C) V
              hV)
            (hπ.locallyOfFiniteTypeComp r p)
            (AffineChart.jOver C V π hπ A p) 0
            (AffineChart.j_flat C V π hπ A)
            (AffineChart.j_relativeDimension C V π hπ A))) := sorry

end AlgebraicGeometry
