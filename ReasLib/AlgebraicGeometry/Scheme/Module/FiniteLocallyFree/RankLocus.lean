module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Rank loci of finite locally free modules

The fiber-rank level sets of a finite locally free module are bundled as clopen
subsets, together with their covering, disjointness, and pullback properties.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Finite local freeness makes the fiber-rank function locally constant. -/
instance instIsFiberRankLocallyConstantOfIsFiniteLocallyFree
    (E : X.Modules) [E.IsFiniteLocallyFree] : E.IsFiberRankLocallyConstant := sorry

/-- The locus on which a finite locally free module has fiber rank `r` is clopen. -/
theorem fiberFinrank_isClopen (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) :
    IsClopen {x : X | E.fiberFinrank x = r} := sorry

/-- The clopen locus on which a finite locally free module has fiber rank `r`. -/
noncomputable def rankClopen (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) : Clopens X :=
  ⟨{x : X | E.fiberFinrank x = r}, fiberFinrank_isClopen E r⟩

/-- Membership in `rankClopen E r` means that the fiber rank is `r`. -/
theorem mem_rankClopen (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) (x : X) :
    x ∈ rankClopen E r ↔ E.fiberFinrank x = r := sorry

/-- The clopen rank loci of a finite locally free module cover the scheme. -/
theorem rankClopen_iSup (E : X.Modules) [E.IsFiniteLocallyFree] :
    iSup (fun r : ℕ ↦ (rankClopen E r).toOpens) = ⊤ := sorry

/-- Distinct clopen rank loci of a finite locally free module are disjoint. -/
theorem rankClopen_pairwiseDisjoint (E : X.Modules) [E.IsFiniteLocallyFree] :
    Pairwise (fun r s : ℕ ↦
      Disjoint (rankClopen E r : Set X) (rankClopen E s : Set X)) := sorry

/-- Rank loci commute with pullback along locally finite-type morphisms. -/
theorem rankClopen_pullback {Y : Scheme.{u}} (E : X.Modules) [E.IsFiniteLocallyFree]
    (g : Y ⟶ X) [LocallyOfFiniteType g] (r : ℕ) :
    (rankClopen ((pullback g).obj E) r : Set Y) =
      g ⁻¹' (rankClopen E r : Set X) := sorry

/-- Restricting a finite locally free module to its rank-`r` locus gives constant rank `r`. -/
instance rankClopenPullback_isFiniteLocallyFreeOfRank
    (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) :
    IsFiniteLocallyFreeOfRank r
      ((pullback (Scheme.Opens.ι (rankClopen E r).toOpens)).obj E) := sorry

end AlgebraicGeometry.Scheme.Modules
