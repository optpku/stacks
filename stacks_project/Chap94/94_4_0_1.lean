module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.CategoryTheory.Fibered.Representable.Presentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

variable {S : Scheme.{u}}
variable {P Q : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)}
variable {U V : Over S}
variable (eP : P ≌ slice U) (eQ : Q ≌ slice V)
variable (f : U ⟶ V) {F G : P ⟶ Q}
variable (hF : InducesHom F eP.hom eQ.hom f)
variable (hG : InducesHom G eP.hom eQ.hom f)

/- 94.4.0.1: if categories fibred in groupoids `P`, `Q` over `Over S` are
representable by schemes `U`, `V` over `S`, then `1`-morphisms `P ⟶ Q` modulo
`2`-isomorphism are identified with morphisms `U ⟶ V` in `Over S`. -/
@[stacks 04SR]
#check (CategoryTheory.FiberedCategoryOver.Groupoids.Presentation.homEquiv eP eQ :
  (Bicategory.HomotopyCategory.mk P ⟶ Bicategory.HomotopyCategory.mk Q) ≃ (U ⟶ V))

/- Any `1`-morphism `P ⟶ Q` determines a morphism `U ⟶ V` of schemes over `S`. -/
#check (Presentation.recover eP eQ : (P ⟶ Q) → (U ⟶ V))

/- Conversely, every morphism `U ⟶ V` of schemes over `S` is induced by a
`1`-morphism `P ⟶ Q`. -/
#check (InducesHom.exists_morphism eP eQ f :
  ∃ H : P ⟶ Q, InducesHom H eP.hom eQ.hom f)

/- Two `1`-morphisms inducing the same morphism `U ⟶ V` are `2`-isomorphic. -/
#check (InducesHom.nonempty_iso eP eQ f hF hG : Nonempty (F ≅ G))

/- The `2`-isomorphism between two inducing `1`-morphisms is unique. -/
#check (InducesHom.subsingleton_iso eP eQ f hF hG : Subsingleton (F ≅ G))
