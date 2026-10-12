/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap76.Lemma_76_5_3_Map
public import stacks_project.Chap78.Definition_78_18_1_Invariant
public import stacks_project.Chap78.Lemma_78_11_2_Groupoid
public import stacks_project.Chap79.«79_5_1_1_Infinitesimal»

/-!
# Identity of the conormal comparison of an infinitesimal source section

If `s` and `t` are flat, an infinitesimal source section `δ` of a groupoid in
algebraic spaces induces the identity on `Hom.conormalSheaf ι`
via the Lemma 76.5.3 comparison of `f = t ∘ δ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicGeometry.AlgebraicSpace
open Hom

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
variable {U₀ : AlgebraicSpace S} (ι : U₀ ⟶ G.U.left)
variable [IsFirstOrderThickening ι] (δ : InfinitesimalSection G ι)

/-- The morphism `f = t ∘ δ : U ⟶ U` of an infinitesimal source section. -/
def InfinitesimalSection.target : G.U.left ⟶ G.U.left :=
  (δ.arrow ≫ G.t).left

/-- Unfolding of `InfinitesimalSection.target`. -/
theorem InfinitesimalSection.target_eq :
    InfinitesimalSection.target G ι δ = (δ.arrow ≫ G.t).left :=
  rfl

/-- The identity-on-`U₀` square of `f = t ∘ δ`, the input of `Hom.Conormal.map`. -/
theorem InfinitesimalSection.targetCommSq :
    CommSq (𝟙 U₀) ι ι (InfinitesimalSection.target G ι δ) :=
  sorry

/-- The canonical comparison of conormal sheaves induced by `f = t ∘ δ`, as an
endomorphism of `Hom.conormalSheaf ι` after the identity-pullback
correction. -/
def InfinitesimalSection.conormalMap :
    conormalSheaf ι ⟶ conormalSheaf ι :=
  (SmallEtaleModuleGlueing.modulesPullbackId U₀).inv.app
      (conormalSheaf ι) ≫
    Conormal.map (InfinitesimalSection.targetCommSq G ι δ)

/-- Unfolding of `InfinitesimalSection.conormalMap`. -/
theorem InfinitesimalSection.conormalMap_eq :
    InfinitesimalSection.conormalMap G ι δ =
      (SmallEtaleModuleGlueing.modulesPullbackId U₀).inv.app
          (conormalSheaf ι) ≫
        Conormal.map (InfinitesimalSection.targetCommSq G ι δ) :=
  rfl

/-- Lemma 79.5.1: In the situation of this section, let `δ ∈ Γ₀` and
`f = t ∘ δ : U ⟶ U`. If `s` and `t` are flat and `U₀` is `R`-invariant,
then the canonical map
`Hom.conormalSheaf ι ⟶ Hom.conormalSheaf ι`
induced by `f` (More on Morphisms of Spaces, Lemma 76.5.3) is the identity. -/
@[stacks 0CKD]
theorem InfinitesimalSection.conormalMap_eq_id
    [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
    (h_invariant : G.toPreRelation.IsInvariant (Subobject.mk ι)) :
    InfinitesimalSection.conormalMap G ι δ =
      𝟙 (conormalSheaf ι) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
