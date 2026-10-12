/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Lemma_85_2_8_Morphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialObject

universe u

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)

/- Canonical morphism of topoi `a : Sh(Y_Zar) ⟶ Sh(X)` induced by an augmentation. -/
#check @augmentationMorphism

/- Lemma 85.2.8 (1): `a⁻¹ F` restricts on `Y_n` to `a_n⁻¹ F`. -/
@[stacks 09W4] #check @inverseImage_component

/- Lemma 85.2.8 (2): `a_m ∘ Y(φ) = a_n` for all `φ : ⦋m⦌ ⟶ ⦋n⦌`. -/
@[stacks 09W4] #check @component_naturality

/- Lemma 85.2.8 (3): `a ∘ g_n = a_n` as morphisms of topoi. -/
@[stacks 09W4] #check @comp_component

/- Lemma 85.2.8 (4): `a_* G` is the equalizer of `a_{0,*} G_0 ⇉ a_{1,*} G_1`. -/
@[stacks 09W4] #check @pushforwardFork_isLimit
