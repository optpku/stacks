/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.Pushforward.SectionFamilies
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat.Sheaf

noncomputable section

universe u v

/- The pullback-pushforward adjunction is the canonical owner of the bijection between maps
`f⁻¹𝒢 ⟶ ℱ` and maps `𝒢 ⟶ f_*ℱ`. The compatible-family equivalence is independent of the
coefficient universe, while mathlib's sheaf pullback currently ties that universe to the spaces
for the direct adjunction recall. -/

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable (𝒢₀ : Y.Sheaf (Type u)) (ℱ₀ : X.Sheaf (Type u))
variable (𝒢 : Y.Sheaf (Type v)) (ℱ : X.Sheaf (Type v))

/- Lemma 6.21.8 (1): the first and second sets in the source are canonically equivalent by the
pullback-pushforward adjunction, functorially in both sheaves. -/
@[stacks 008K "pullback-pushforward adjunction bijection"]
#check (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv 𝒢₀ ℱ₀

/- Lemma 6.21.8 (3): the third set in the source, namely maps of sheaves over `f`. -/
@[stacks 008K "the f-map hom set"]
#check (𝒢 ⟶ (TopCat.Sheaf.pushforward (Type v) f).obj ℱ)

/- Lemma 6.21.8 (3)-(4): maps `𝒢 ⟶ f_*ℱ`, hence the `f`-maps of Definition 6.21.7, are canonically
equivalent to compatible collections of maps `𝒢(V) ⟶ ℱ(U)` for all opens `U ⊆ f⁻¹(V)`. -/
@[stacks 008K "compatible two-open-set families"]
#check ContinuousMapSheafMapFamily.homEquiv (f := f) (𝒢 := 𝒢) (ℱ := ℱ)

/- The two canonical equivalences compose to the source-facing equivalence between maps from
`f⁻¹𝒢` and compatible two-open-set families. -/
@[stacks 008K "pullback maps and compatible families"]
#check
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv 𝒢₀ ℱ₀).trans
    (ContinuousMapSheafMapFamily.homEquiv (f := f) (𝒢 := 𝒢₀) (ℱ := ℱ₀))
