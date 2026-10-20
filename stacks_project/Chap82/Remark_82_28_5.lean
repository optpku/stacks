module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RankLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.RankChowProduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.RankGluedChern

/-!
# Chern classes of finite locally free modules of non-constant rank

In Situation 82.2.1, a finite locally free module on a good algebraic space
decomposes into clopen rank loci. Chern classes are the identity bivariant
classes that preserve the resulting Chow-group product and act by the
constant-rank operations on each factor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.ChernClass
open TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChernClass

section

variable {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E]
    (g : Y ⟶ X) [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (i r : ℕ) (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k)

/- The clopen rank loci cover the space and are pairwise disjoint. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.rankClopen_iSup E :
  iSup (fun r : ℕ ↦ (rankClopen E r).toOpens) = ⊤)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.rankClopen_pairwiseDisjoint E :
  Pairwise fun r s : ℕ ↦
    Disjoint (rankClopen E r : Set (Points X)) (rankClopen E s : Set (Points X)))

/- Pullback induces the corresponding rank decomposition on every test space. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.rankClopen_pullback E g r :
  (rankClopen ((pullback g).obj E) r : Set (Points Y)) =
    Points.map g ⁻¹' (rankClopen E r : Set (Points X)))

/- In every integer degree, the Chow group is the full product of the rank factors. -/
#check (AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.pullbackRankProduct E f δ k g :
  Hom.chowGroup (g ≫ f) δ k ≃+
    ∀ r : ℕ, Hom.chowGroup
      ((rankOpenSubspace ((pullback g).obj E) r).ι ≫ (g ≫ f)) δ k)

/- Remark 82.28.5: A finite locally free module on a good algebraic space
splits along its clopen rank loci. Pullback preserves this decomposition,
and the Chow groups of each good test space are products of the rank factors.
Its Chern classes are bivariant classes for the identity morphism: they
preserve these products and act by the constant-rank Chern operations on each
factor. Such a module can have nonzero Chern classes in infinitely many degrees. -/
@[stacks 0ES2] #check (AlgebraicGeometry.AlgebraicSpace.ChernClass.chernClass_component
    δ f E g i r k α :
  chowProductEquiv δ (g ≫ f) ((pullback g).obj E) (k - (i : ℤ))
      ((chernClass δ f E i).cap g k α) r =
    rankwiseCap δ (g ≫ f) ((pullback g).obj E) i r k
      (chowProductEquiv δ (g ≫ f) ((pullback g).obj E) k α r))

end

/- A single finite locally free module need not have an eventual vanishing bound. -/
#check (AlgebraicGeometry.AlgebraicSpace.ChernClass.chernClass_not_eventually_zero :
    ¬ ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
        [UniversallyCatenary B] [IsQuasiSeparated B]
        (δ : Points B → ℤ) [IsDimensionFunction δ]
        {X : AlgebraicSpace S} (f : X ⟶ B)
        [QuasiSeparated f] [LocallyOfFiniteType f]
        (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E],
      ∃ N : ℕ, ∀ i : ℕ, N < i →
        chernClass δ f E i = ChowCohomology.zeroCap δ f (i : ℤ))

end AlgebraicGeometry.AlgebraicSpace.ChernClass
