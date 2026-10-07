module

public import stacks_project.Chap96.Remark_96_6_3_Flat
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.StandardTopology.Big
open scoped Bicategory

universe u

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)

/- Remark 96.6.3 (1): in the situation of Lemma 96.6.2, the morphism of ringed topoi
`associatedRingedToposHom f τ : Sh(X_τ) ⟶ Sh(Y_τ)` is flat, as is clear from the
identification `f⁻¹ 𝒪_Y ≅ 𝒪_X`. This is a bit counter-intuitive, for example because
a closed immersion of algebraic stacks is typically not flat as a morphism of algebraic
stacks. -/
@[stacks 06TX] #check
  (associatedRingedToposHom_isFlat f τ :
    RingedSite.ToposHom.IsFlat.{u + 1, u, u + 1, u, u}
      (associatedRingedToposHom f τ))

variable {T U : Scheme.{u}} (i : T ⟶ U)

/- Remark 96.6.3 (2): the same site-level flatness holds for a closed immersion of
schemes `i : X ⟶ Y`, and in fact for every scheme morphism: the induced morphism of
big `τ`-sites `(Sch/X)_τ ⟶ (Sch/Y)_τ` is `pullbackRingedHom τ i`, which is flat. -/
@[stacks 06TX] #check
  (pullbackRingedHom_isFlat i τ :
    RingedSite.Hom.IsFlat.{u} (pullbackRingedHom τ i))
