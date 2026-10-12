/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Family.UniversalEffectiveEpi
import StacksCheckRecall

@[expose] public section

universe w v u

open CategoryTheory

/- Definition 7.12.1 (1): a family `{Uᵢ ⟶ U}` is an effective epimorphism when every
`Uᵢ ⟶ U` is representable and, for every object `X`, the Hom-fork
`Mor(U, X) ⟶ ∏ᵢ Mor(Uᵢ, X) ⇉ ∏_{(i,j)} Mor(Uᵢ ×_U Uⱼ, X)` is an equalizer. -/
@[stacks 00WP "(1)"]
#check
  (@SemiRepresentableFamily.Over.IsEffectiveEpiFamily.{w, v, u} :
    ∀ {C : Type u} [Category.{v} C] {U : C},
      SemiRepresentableFamily.Over.{w} U → Prop)

/- Definition 7.12.1 (2): a family `{Uᵢ ⟶ U}` is a universal effective epimorphism when
for every morphism `V ⟶ U` the base change `{Uᵢ ×_U V ⟶ V}` is an effective
epimorphism. -/
@[stacks 00WP "(2)"]
#check
  (@SemiRepresentableFamily.Over.IsUniversalEffectiveEpiFamily.{w, v, u} :
    ∀ {C : Type u} [Category.{v} C] {U : C},
      SemiRepresentableFamily.Over.{w} U → Prop)

#check @EffectiveEpiFamily
#check @SemiRepresentableFamily.Over.baseChange
#check @SemiRepresentableFamily.Over.IsUniversalEffectiveEpiFamily.toIsEffectiveEpiFamily
