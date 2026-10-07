module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass
public import ReasLib.AlgebraicGeometry.ChowCohomology.FirstChern.Commutation

@[expose] public section

open CategoryTheory
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChowCohomology.ChernClass

/-- The two orders of lowering a Chow degree by natural numbers `i` and `j`
have the same resulting degree. -/
theorem capCommDegree (k : ℤ) (i j : ℕ) :
    (k - (j : ℤ)) - (i : ℤ) = (k - (i : ℤ)) - (j : ℤ) := sorry

/-- Every finite-support graded bivariant class commutes degreewise with the
canonical Chern component after pullback of the finite locally free module. -/
theorem comp_component
    {S X X' : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ)
    [IsDimensionFunction δ] (p : X ⟶ S) [LocallyOfFiniteType p]
    (f : X' ⟶ X) [LocallyOfFiniteType f] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (j : ℕ)
    (c : @DirectSum ℤ
      (fun q ↦ BivariantClass δ (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p) q)
      (fun q ↦ (BivariantClass.pointwiseAddCommGroup δ
        (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p) q).toAddCommMonoid)) :
    ∀ q : ℤ, HEq
      (BivariantClass.comp δ (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p)
        (𝟙 (Over.mk p)) (c q) (component δ p E r j))
      (BivariantClass.comp δ (𝟙 (Over.mk (f ≫ p)))
        (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p)
        (component δ (f ≫ p) ((Scheme.Modules.pullback f).obj E) r j) (c q)) := sorry

/-- Every canonical Chern component belongs to the center of the full Chow
cohomology ring. -/
theorem component_mem_center
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (j : ℕ) :
    DirectSum.of (degree δ p) (j : ℤ) (component δ p E r j) ∈
      Set.center (ring δ p) := sorry

/-- Cap operations by Chern components of two finite locally free modules
commute on every relative Chow class. -/
theorem component_cap_comm
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p]
    (E : X.Modules) (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (F : X.Modules) (s : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank s F]
    (i j : ℕ) (k : ℤ) (α : RelativeChow δ (Over.mk p) k) :
    castDegree δ (Y := Over.mk p) (capCommDegree k i j)
        (chowCap δ p E r i (k - (j : ℤ)) (chowCap δ p F s j k α)) =
      chowCap δ p F s j (k - (i : ℤ)) (chowCap δ p E r i k α) := sorry

end AlgebraicGeometry.ChowCohomology.ChernClass
