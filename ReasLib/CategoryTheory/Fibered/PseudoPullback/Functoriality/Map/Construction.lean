/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Cospan.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Construction of maps between explicit pseudo-pullbacks

The componentwise owner induced by a based cospan transformation, together with its strict
compatibility with the common base projection.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor

universe u v
universe uX₁ vX₁ uY₁ vY₁ uS₁ vS₁
universe uX₂ vX₂ uY₂ vY₂ uS₂ vS₂

namespace CategoryTheory

open Bicategory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback

noncomputable section

variable {X₁ : BasedCategory.{vX₁, uX₁} C}
variable {Y₁ : BasedCategory.{vY₁, uY₁} C}
variable {S₁ : BasedCategory.{vS₁, uS₁} C}
variable {X₂ : BasedCategory.{vX₂, uX₂} C}
variable {Y₂ : BasedCategory.{vY₂, uY₂} C}
variable {S₂ : BasedCategory.{vS₂, uS₂} C}
variable {F₁ : X₁ ⥤ᵇ S₁} {G₁ : Y₁ ⥤ᵇ S₁}
variable {F₂ : X₂ ⥤ᵇ S₂} {G₂ : Y₂ ⥤ᵇ S₂}

namespace Implementation

/-- The object of the target pseudo-pullback obtained by applying a cospan transformation to a
source object. The target comparison is the symmetric three-step pasting
`leftIso.hom ≪≫ base.mapIso P.iso ≪≫ rightIso.inv` in the common fiber. -/
private def mapObj
    (psi : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) : (PseudoPullback F₂ G₂).obj :=
  mk F₂ G₂ (baseObj P)
    ((CategoricalPullback.map (psi.fiber (baseObj P))).obj (fiberObj P))

/-- The component maps obtained from a cospan transformation satisfy the target comparison
square. This is naturality of the two boundary isomorphisms pasted with the source square. -/
private theorem mapMap_comm
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    {P Q : (PseudoPullback F₁ G₁).obj} (φ : P ⟶ Q) :
    CommSq
      (F₂.toFunctor.map (ψ.left.map (fstMap φ)))
      (comparison (mapObj ψ P))
      (comparison (mapObj ψ Q))
      (G₂.toFunctor.map (ψ.right.map (sndMap φ))) := sorry
/- Proof strategy: unfold `mapObj`; reassociate the three comparison factors and paste the
naturality squares of `ψ.leftIso` and `ψ.rightIso` around the image under `ψ.base` of
`comm F₁ G₁ φ`. -/

/-- The mapped first component lifts the unchanged common base map. -/
private theorem mapMap_fst_isHomLift
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    {P Q : (PseudoPullback F₁ G₁).obj} (φ : P ⟶ Q) :
    X₂.p.IsHomLift (baseMap φ) (ψ.left.map (fstMap φ)) := sorry
-- Proof strategy: combine the source lift instance with preservation of lifts by ψ.left.

/-- The mapped second component lifts the unchanged common base map. -/
private theorem mapMap_snd_isHomLift
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    {P Q : (PseudoPullback F₁ G₁).obj} (φ : P ⟶ Q) :
    Y₂.p.IsHomLift (baseMap φ) (ψ.right.map (sndMap φ)) := sorry
-- Proof strategy: combine the source lift instance with preservation of lifts by ψ.right.

/-- The morphism of target pseudo-pullback objects induced componentwise by a cospan
transformation. Its common base arrow is unchanged. -/
private def mapMap
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    {P Q : (PseudoPullback F₁ G₁).obj} (φ : P ⟶ Q) : mapObj ψ P ⟶ mapObj ψ Q :=
  PseudoPullback.Hom.mk (baseMap (P := P) (Q := Q) φ)
    (ψ.left.map (fstMap φ)) (mapMap_fst_isHomLift ψ φ)
    (ψ.right.map (sndMap φ)) (mapMap_snd_isHomLift ψ φ)
    (mapMap_comm ψ φ)

/-- The componentwise pseudo-pullback map preserves identity morphisms. -/
private theorem mapMap_id
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    mapMap ψ (𝟙 P) = 𝟙 (mapObj ψ P) := sorry
/- Proof strategy: apply `hom_ext`; both projected components reduce to functoriality of
`ψ.left` and `ψ.right`, while the common base component is definitionally unchanged. -/

/-- The componentwise pseudo-pullback map preserves composition. -/
private theorem mapMap_comp
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    {P Q R : (PseudoPullback F₁ G₁).obj} (φ : P ⟶ Q) (χ : Q ⟶ R) :
    mapMap ψ (φ ≫ χ) = mapMap ψ φ ≫ mapMap ψ χ := sorry
/- Proof strategy: apply `hom_ext`; use `Functor.map_comp` independently on the left and right
components. The pseudo-pullback comparison law is proof-valued and disappears under
extensionality. -/

/-- The ordinary functor on explicit pseudo-pullbacks induced by a cospan transformation. -/
private def mapFunctor
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂) :
    (PseudoPullback F₁ G₁).obj ⥤ (PseudoPullback F₂ G₂).obj where
  obj := mapObj ψ
  map := mapMap ψ
  map_id := mapMap_id ψ
  map_comp := mapMap_comp ψ

/-- The ordinary pseudo-pullback map retains the common base projection. -/
private theorem mapFunctor_comp_projection
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂) :
    mapFunctor ψ ⋙ (PseudoPullback F₂ G₂).p = (PseudoPullback F₁ G₁).p := sorry

end Implementation

/-- The computational pseudo-pullback map induced by a based cospan transformation.
Unlike the semantic bilimit lift, its object and morphism components are the explicit fiberwise
three-step pasting and component maps. -/
@[stacks 0040 "map of explicit pseudo-pullbacks induced by a cospan transformation"]
def map
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂) :
    PseudoPullback F₁ G₁ ⥤ᵇ PseudoPullback F₂ G₂ where
  toFunctor := Implementation.mapFunctor ψ
  w := Implementation.mapFunctor_comp_projection ψ

/-- The explicit pseudo-pullback map strictly preserves the common base projection. -/
theorem map.compProjection
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂) :
    (map ψ).toFunctor ⋙ (PseudoPullback F₂ G₂).p =
      (PseudoPullback F₁ G₁).p := sorry

end

end PseudoPullback

end BasedCategory

end CategoryTheory
