/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.CategoryTheory.Sites.Topos.Morphism

/-!
# Composition of base-change maps of topoi

The Beck-Chevalley map of a square of left-exact adjunctions is compatible
with both vertical and horizontal pasting.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.TwoSquare
open scoped MorphismOfTopoiIn TwoSquare

noncomputable section

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈
universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ w

namespace CategoryTheory.MorphismOfTopoiIn

variable {B' : Type u₁} [Category.{v₁} B']
variable {B : Type u₂} [Category.{v₂} B]
variable {C'' : Type u₃} [Category.{v₃} C'']
variable {C' : Type u₄} [Category.{v₄} C']
variable {C : Type u₅} [Category.{v₅} C]
variable {D'' : Type u₆} [Category.{v₆} D'']
variable {D' : Type u₇} [Category.{v₇} D']
variable {D : Type u₈} [Category.{v₈} D]
variable {JB' : GrothendieckTopology B'} {JB : GrothendieckTopology B}
variable {JC'' : GrothendieckTopology C''} {JC' : GrothendieckTopology C'}
variable {JC : GrothendieckTopology C}
variable {JD'' : GrothendieckTopology D''} {JD' : GrothendieckTopology D'}
variable {JD : GrothendieckTopology D}

/-- The Beck-Chevalley transformation obtained by taking the mate of a square
of inverse-image functors. -/
noncomputable def baseChange
    (k : MorphismOfTopoiIn JB JB')
    (f' : MorphismOfTopoiIn JC' JB')
    (f : MorphismOfTopoiIn JC JB)
    (l : MorphismOfTopoiIn JC JC')
    (square : TwoSquare (l⁻¹) (f⁻¹) (f'⁻¹) (k⁻¹)) :
    f.pushforward ⋙ l⁻¹ ⟶ k⁻¹ ⋙ f'.pushforward :=
  (mateEquiv f.adjunction f'.adjunction square).natTrans

/-- The base-change map of two vertically pasted squares is the appropriately associated
composite of their base-change maps. -/
@[stacks 0F6X]
theorem baseChange_vcomp
    (k : MorphismOfTopoiIn JB JB') (l : MorphismOfTopoiIn JC JC')
    (m : MorphismOfTopoiIn JD JD')
    (g' : MorphismOfTopoiIn JD' JC') (g : MorphismOfTopoiIn JD JC)
    (f' : MorphismOfTopoiIn JC' JB') (f : MorphismOfTopoiIn JC JB)
    (upper : TwoSquare (l⁻¹) (f⁻¹) (f'⁻¹) (k⁻¹))
    (lower : TwoSquare (m⁻¹) (g⁻¹) (g'⁻¹) (l⁻¹)) :
    (Functor.associator (f.pushforward) (g.pushforward) (m⁻¹)).hom ≫
        Functor.whiskerLeft (f.pushforward) (baseChange l g' g m lower) ≫
          (Functor.associator (f.pushforward) (l⁻¹) (g'.pushforward)).inv ≫
            Functor.whiskerRight (baseChange k f' f l upper) (g'.pushforward) ≫
              (Functor.associator (k⁻¹) (f'.pushforward) (g'.pushforward)).hom =
      baseChange k (g'.comp f') (g.comp f) m (lower ≫ᵥ upper) := sorry

/-- Base-change maps are compatible with horizontal pasting of squares. -/
theorem baseChange_hcomp
    (g' : MorphismOfTopoiIn JC' JC'') (g : MorphismOfTopoiIn JC JC')
    (f'' : MorphismOfTopoiIn JD'' JC'')
    (f' : MorphismOfTopoiIn JD' JC') (f : MorphismOfTopoiIn JD JC)
    (h' : MorphismOfTopoiIn JD' JD'') (h : MorphismOfTopoiIn JD JD')
    (left : TwoSquare (h'⁻¹) (f'⁻¹) (f''⁻¹) (g'⁻¹))
    (right : TwoSquare (h⁻¹) (f⁻¹) (f'⁻¹) (g⁻¹)) :
    (Functor.associator (f.pushforward) (h⁻¹) (h'⁻¹)).inv ≫
        Functor.whiskerRight (baseChange g f' f h right) (h'⁻¹) ≫
          (Functor.associator (g⁻¹) (f'.pushforward) (h'⁻¹)).hom ≫
            Functor.whiskerLeft (g⁻¹) (baseChange g' f'' f' h' left) ≫
              (Functor.associator (g⁻¹) (g'⁻¹) (f''.pushforward)).inv =
      baseChange (g.comp g') f'' f (h.comp h') (right ≫ₕ left) := sorry

end CategoryTheory.MorphismOfTopoiIn
