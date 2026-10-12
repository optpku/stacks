/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Extension.Sum
public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Extension.SourceSum
public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Extension.ShortComplex
import StacksCheckRecall

@[expose] public section

/-!
@stack 0192

# Source-facing bridge for Lemma 14.22.4

The reusable chain-level model is `ChainComplex.disk`; its Dold-Kan image and the resulting short
exact sequence are owned by the Eilenberg-MacLane extension module.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.eilenbergMacLane

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable (A : 𝒜) (k : ℕ)

/- Lemma 14.22.4 (1): the extension from `K(A, k)` to `K(A, k + 1)` is short exact. -/
@[stacks 0192 "Lemma 14.22.4: short exact extension"]
#check (extension.shortComplex.app.shortExact A k :
  (extension.shortComplex.app A k).ShortExact)

/- Lemma 14.22.4 (2): the extension is split after evaluation in every simplicial degree. -/
@[stacks 0192 "Lemma 14.22.4: degreewise splitting"]
#check (extension.degree.splitting A k :
  ShortComplex.FunctorCategory.PointwiseSplitting
    (extension.shortComplex.app A k))

variable (n : ℕ)

/- The source's final-face convention presents the degree-`n` term as the coproduct indexed by the
two adjacent families of simplex epimorphisms. -/
@[stacks 0192 "Lemma 14.22.4 (1): degreewise coproduct decomposition"]
#check (extension.source.iso A k n :
  (extension.object A k).obj (Opposite.op ⦋n⦌) ≅
    ∐ fun _ : extension.Index k n ↦ A)
#check (extension.source.natIso (𝒜 := 𝒜) k n)
#check (extension.source.natIso.app (𝒜 := 𝒜) k n A)

variable {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) (a : extension.Index k n)

/- In the source's final-face convention, the simplicial structure map sends a summand along the
partial pullback of its indexing epimorphism, and sends it to zero when that pullback is absent. -/
@[stacks 0192 "Lemma 14.22.4 (2): structure map on coproduct summands"]
#check (extension.source.inclusion.map A φ a :
  extension.source.inclusion A a ≫ (extension.object A k).map φ.op =
    Option.elim (extension.Index.last.pull a φ) 0
      (fun b ↦ extension.source.inclusion A b))
#check extension.source.simplex.inclusion
#check extension.source.iso.inclusion_hom
#check extension.source.iso.inclusion_inv
#check extension.source.natIso
#check extension.source.natIso.app
#check extension.source.natIso.inclusion_hom
#check extension.source.natIso.inclusion_inv
#check extension.source.inclusion.map_of_some
#check extension.source.inclusion.map_of_none
#check extension.source.inclusion.rev
#check extension.Index.last.hom
#check extension.Index.last.hom_injective
#check extension.Index.last.pull.rev
#check extension.Index.last.pull.eq_some_iff
#check extension.Index.last.pull.eq_none_iff

/- The canonical d₀-oriented presentation is the same object with the index transported by order
reversal. -/
#check (extension.sum.iso A k n :
  (extension.object A k).obj (Opposite.op ⦋n⦌) ≅
    ∐ fun _ : extension.Index k n ↦ A)
#check (extension.sum.inclusion.map A φ a :
  extension.sum.inclusion A a ≫ (extension.object A k).map φ.op =
    Option.elim (a.pull φ) 0 (fun b ↦ extension.sum.inclusion A b))

#check (ChainComplex.disk A k : ChainComplex 𝒜 ℕ)
#check (ChainComplex.twoTerm (𝟙 A) k : ChainComplex 𝒜 ℕ)
#check (ChainComplex.disk.upperIso A k)
#check (ChainComplex.disk.lowerIso A k)
#check (ChainComplex.disk.d A k)
#check (ChainComplex.disk.functor 𝒜 k)
#check (ChainComplex.disk.shortComplex 𝒜 k)
#check (ChainComplex.disk.shortComplex.app.shortExact A k)
#check (ChainComplex.disk.degreewiseSplitting A k).mapΓ₀
#check (ChainComplex.disk.degreewiseSplitting A k).mapΓ₀.shortExact
#check (extension.object A k : SimplicialObject 𝒜)
#check (extension.functor (𝒜 := 𝒜) k)
#check (extension.shortComplex (𝒜 := 𝒜) k)
#check (extension.shortComplex.app A k : ShortComplex (SimplicialObject 𝒜))
#check (extension.shortComplex.shortExact (𝒜 := 𝒜) k)
#check (extension.shortComplex.app.shortExact A k)
#check (ChainComplex.disk.degree.splitting A k)
#check AlgebraicTopology.DoldKan.Γ₀.additive
#check ShortComplex.FunctorCategory.shortExact_iff_shortExact_app
#check extension.Index
#check extension.sum.inclusion
#check (extension.sum.iso A k)
#check extension.sum.iso.hom
#check extension.sum.iso.inv
#check extension.sum.iso.inclusion_hom
#check extension.sum.iso.inclusion_inv
#check extension.sum.inclusion.map
#check extension.sum.inclusion.map_of_some
#check extension.sum.inclusion.map_of_none

end CategoryTheory.SimplicialObject.eilenbergMacLane
