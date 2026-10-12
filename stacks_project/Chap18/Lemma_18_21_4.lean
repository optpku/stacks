/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Sheaf.Relocalization
import StacksCheckRecall

/-!
# Lemma 18.21.4

Compatibility facade for relocalization along a map of sheaves.  The
reusable owner is the morphism of ringed topoi and its canonical invertible
triangle with the ambient localization maps.  The slice-topos comparison is
retained as a low-level view.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Sheaf.Localization

noncomputable section

universe u v

namespace RingedSite.Localization.AtSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (O : Sheaf J RingCat.{max u v})
variable {G F : Sheaf J (Type v)} (s : G ⟶ F)

/- The inverse-image comparison identifies the two localized structure
rings before passing to its adjoint direct-image structure map. -/
@[stacks 04J4 "inverse-image structure comparison"]
#check relocalizationInverseImageStructureIso O s

variable [∀ P : G.obj.Elementsᵒᵖᵒᵖ ⥤ RingCat.{max u v},
  (relocalizationFunctor s).op.HasPointwiseRightKanExtension P]

/- The direct-image structure map is characterized as the adjoint transpose
of the canonical inverse-image comparison. -/
@[stacks 04J4 "structure-map compatibility"]
#check relocalizationStructureMap_adjunct O s

variable [∀ P : G.obj.Elementsᵒᵖᵒᵖ ⥤ Type (max u v),
  (relocalizationFunctor s).op.HasPointwiseRightKanExtension P]

/- Lemma 18.21.4 (04J4): relocalization between the category-of-elements
localizations is a morphism of ringed topoi. -/
@[stacks 04J4 "ringed-topos relocalization"]
#check (relocalization O s : ToposHom (site O G) (site O F))

section Triangle

variable [∀ P : F.obj.Elementsᵒᵖᵒᵖ ⥤ RingCat.{max u v},
  (localizationProjection F).op.HasPointwiseRightKanExtension P]
variable [∀ P : G.obj.Elementsᵒᵖᵒᵖ ⥤ RingCat.{max u v},
  (localizationProjection G).op.HasPointwiseRightKanExtension P]
variable [∀ P : F.obj.Elementsᵒᵖᵒᵖ ⥤ Type (max u v),
  (localizationProjection F).op.HasPointwiseRightKanExtension P]
variable [∀ P : G.obj.Elementsᵒᵖᵒᵖ ⥤ Type (max u v),
  (localizationProjection G).op.HasPointwiseRightKanExtension P]

/- Lemma 18.21.4 (04J4): relocalization followed by the localization at `F`
is canonically `2`-isomorphic to the localization at `G`. -/
@[stacks 04J4 "ringed-topos triangle"]
#check (relocalizationTriangle O s :
  ToposHom.TwoIso (X := site O G) (Y := ofRingSheaf J O)
    (relocalizationToAmbient O s) (toAmbient O G))

end Triangle

/- Lemma 18.21.4 (04J4): for `s : G ⟶ F`, relocalization is the canonical
isomorphism `Over.star F ⋙ Over.pullback s ≅ Over.star G`. -/
@[stacks 04J4 "inverse image"]
#check Over.starPullbackIsoStar s

section SliceTopos

variable {G₀ F₀ : Sheaf J (Type (max u v))} (s₀ : G₀ ⟶ F₀)

/- Applying the same isomorphism to the underlying structure sheaf gives
the ringed structure-object comparison, with compatibility encoded by its
being an isomorphism in `Over G₀`. -/
@[stacks 04J4 "structure object"]
#check underlyingStructurePullbackIso O s₀

end SliceTopos

end RingedSite.Localization.AtSheaf
