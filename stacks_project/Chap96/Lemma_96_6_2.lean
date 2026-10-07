module

public import stacks_project.Chap96.Lemma_96_6_2_RingedTopos
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)

/- The canonical identification `f⁻¹ 𝒪_Y ≅ 𝒪_X` of associated `τ`-structure sheaves. -/
#check (associatedStructureSheafInverseImageIso f τ :
  ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
      (X.associatedTopology τ) (Y.associatedTopology τ)).obj
    (associatedStructureSheaf Y τ) ≅ associatedStructureSheaf X τ)

/- Lemma 96.6.2: let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. Let `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.
There is a canonical identification `f⁻¹ 𝒪_𝒴 ≅ 𝒪_𝒳` which turns
`f : Sh(𝒳_τ) ⟶ Sh(𝒴_τ)` into a morphism of ringed topoi. -/
@[stacks 06TW] #check
  (associatedRingedToposHom f τ :
    RingedSite.ToposHom (associatedRingedSite X τ) (associatedRingedSite Y τ))
