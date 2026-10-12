/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap102.Definition_102_3_1_LimitPreserving
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change of limit-preserving 1-morphisms

The base change of a limit-preserving 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf` along an arbitrary 1-morphism is again limit
preserving.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace LimitPreserving

/-- Lemma 102.3.3: Let `p : 𝒳 ⟶ 𝒴` and `q : 𝒵 ⟶ 𝒴` be 1-morphisms of
categories fibred in groupoids over `(Sch/S)_fppf`. If `p` is limit
preserving, then so is the base change `p' : 𝒳 ×_𝒴 𝒵 ⟶ 𝒵` of `p` by `q`,
identified with `TwoFibreProduct.snd p q : TwoFibreProduct.apex p q ⟶ 𝒵`. -/
@[stacks 0CMT]
instance pullback_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Z ⟶ Y) [LimitPreserving p] :
    LimitPreserving (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) := sorry

end LimitPreserving

end AlgebraicGeometry.Groupoids.Hom
