module

public import stacks_project.Chap82.Remark_82_28_5_RankLocus
public import stacks_project.Chap82.Remark_82_28_5_ChernClass

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

/-- Remark 82.28.5 (1): In Situation 82.2.1, for good `X / B` and a finite
locally free `𝒪_X`-module `E`, write `X = ⨿_r X_r` as the coproduct of the
open-and-closed rank-`r` subspaces `rankOpenSubspace E r`, equivalently the
covering and pairwise-disjoint clopen loci `rankClopen E r`. -/
@[stacks 0ES2]
theorem rankOpenSubspace_coproduct {S : Scheme.{u}} {B : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    {X : AlgebraicSpace S} (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E] :
    iSup (fun r : ℕ ↦ (rankClopen E r).toOpens) = ⊤ ∧
      Pairwise fun r s : ℕ ↦
        Disjoint (rankClopen E r : Set (Points X))
          (rankClopen E s : Set (Points X)) :=
  sorry

/-- Remark 82.28.5 (2): If `X' ⟶ X` is a morphism of good algebraic spaces over
`B`, pullback yields the corresponding rank decomposition of `X'`. -/
@[stacks 0ES2]
theorem rankDecomposition_pullback {S : Scheme.{u}} {B : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    {X Y : AlgebraicSpace S} (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E]
    (g : Y ⟶ X) [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (r : ℕ) :
    (rankClopen ((pullback g).obj E) r : Set (Points Y)) =
      Points.map g ⁻¹' (rankClopen E r : Set (Points X)) :=
  sorry

/-- Remark 82.28.5 (3): The pulled-back rank decomposition identifies Chow
groups `CH_*(X') ≃+ ∏_r CH_*(X'_r)` by restriction to the rank loci. -/
@[stacks 0ES2]
theorem chowGroup_product_rankLoci {S : Scheme.{u}} {B : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    {X Y : AlgebraicSpace S} (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E]
    (g : Y ⟶ X) [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (k : ℤ) :
    Function.Bijective
      (fun α : chowGroup (g ≫ f) δ k ↦
        fun r : ℕ ↦
          openPullback (g ≫ f) δ (rankOpenSubspace ((pullback g).obj E) r) k α) :=
  sorry

/-- Remark 82.28.5 (4): The Chern class `c_i(E)` is the bivariant identity
class in `A^i(X)` which preserves these product decompositions and acts by
the already-defined constant-rank operations `c_i(E|_{X_r}) ∩ -` on the
factors. In this setting `c_i(E)` may be nonzero for infinitely many `i`. -/
@[stacks 0ES2]
theorem chernClass_preserves_product {S : Scheme.{u}} {B : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    {X Y : AlgebraicSpace S} (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E]
    (g : Y ⟶ X) [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (i r : ℕ) (k : ℤ) (α : chowGroup (g ≫ f) δ k) :
    chowProductEquiv δ (g ≫ f) ((pullback g).obj E) (k - (i : ℤ))
        ((chernClass δ f E i).cap g k α) r =
      rankwiseCap δ (g ≫ f) ((pullback g).obj E) i r k
        (chowProductEquiv δ (g ≫ f) ((pullback g).obj E) k α r) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ChernClass
