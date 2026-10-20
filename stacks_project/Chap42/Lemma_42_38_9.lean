module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Commutation
public import ReasLib.AlgebraicGeometry.BivariantClass.Commutation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped DirectSum

noncomputable section

universe u

/- Lemma 42.38.9 (1): each Chern component of a finite locally free module is
central in the full Chow cohomology ring. -/
@[stacks 02UA] #check
  (AlgebraicGeometry.ChowCohomology.ChernClass.component_mem_center :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ)
      [IsDimensionFunction δ] (p : X ⟶ S) [LocallyOfFiniteType p]
      (E : X.Modules) (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
      (j : ℕ),
      DirectSum.of (ChowCohomology.degree δ p) (j : ℤ)
          (ChowCohomology.ChernClass.component δ p E r j) ∈
        Set.center (ChowCohomology.ring δ p))

/- Lemma 42.38.9 (2): every finite-support graded bivariant class commutes,
degreewise, with the canonical Chern component after pulling the finite locally
free module back. -/
@[stacks 02UA] #check
  (AlgebraicGeometry.ChowCohomology.ChernClass.comp_component :
    ∀ {S X X' : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ)
      [IsDimensionFunction δ] (p : X ⟶ S) [LocallyOfFiniteType p]
      (f : X' ⟶ X) [LocallyOfFiniteType f] (E : X.Modules) (r : ℕ)
      [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (j : ℕ)
      (c : @DirectSum ℤ
        (fun q ↦ BivariantClass δ
          (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p) q)
        (fun q ↦ (BivariantClass.pointwiseAddCommGroup δ
          (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p) q).toAddCommMonoid)),
      ∀ q : ℤ, HEq
        (BivariantClass.comp δ
          (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p)
          (𝟙 (Over.mk p)) (c q)
          (ChowCohomology.ChernClass.component δ p E r j))
        (BivariantClass.comp δ (𝟙 (Over.mk (f ≫ p)))
          (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p)
          (ChowCohomology.ChernClass.component δ (f ≫ p)
            ((Scheme.Modules.pullback f).obj E) r j) (c q)))

/- Lemma 42.38.9 (3): cap operations by Chern components of two finite locally
free modules commute on every relative Chow class. -/
@[stacks 02UA] #check
  (AlgebraicGeometry.ChowCohomology.ChernClass.component_cap_comm :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ)
      [IsDimensionFunction δ] (p : X ⟶ S) [LocallyOfFiniteType p]
      (E : X.Modules) (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
      (F : X.Modules) (s : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank s F]
      (i j : ℕ) (k : ℤ) (α : RelativeChow δ (Over.mk p) k),
      RelativeChow.castDegree δ (X := Over.mk p)
          (ChowCohomology.ChernClass.capCommDegree k i j)
          (ChowCohomology.ChernClass.chowCap δ p E r i (k - (j : ℤ))
            (ChowCohomology.ChernClass.chowCap δ p F s j k α)) =
        ChowCohomology.ChernClass.chowCap δ p F s j (k - (i : ℤ))
          (ChowCohomology.ChernClass.chowCap δ p E r i k α))
