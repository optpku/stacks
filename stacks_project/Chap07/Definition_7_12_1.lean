module

public import ReasLib.CategoryTheory.Sites.Family.UniversalEffectiveEpi
import StacksCheckRecall

@[expose] public section

universe w v u

open CategoryTheory

variable {C : Type u} [Category.{v} C] {U : C}

/- Definition 7.12.1 (1): a family `{Uᵢ ⟶ U}` is an effective epimorphism when every
`Uᵢ ⟶ U` is representable and, for every object `X`, the Hom-fork
`Mor(U, X) ⟶ ∏ᵢ Mor(Uᵢ, X) ⇉ ∏_{(i,j)} Mor(Uᵢ ×_U Uⱼ, X)` is an equalizer. -/
@[stacks 00WP]
#check
  (CategoryTheory.SemiRepresentableFamily.Over.IsEffectiveEpiFamily :
    SemiRepresentableFamily.Over.{w} U → Prop)

/- Definition 7.12.1 (2): a family `{Uᵢ ⟶ U}` is a universal effective epimorphism when
for every morphism `V ⟶ U` the base change `{Uᵢ ×_U V ⟶ V}` is an effective
epimorphism. -/
@[stacks 00WP]
#check
  (CategoryTheory.SemiRepresentableFamily.Over.IsUniversalEffectiveEpiFamily :
    SemiRepresentableFamily.Over.{w} U → Prop)
