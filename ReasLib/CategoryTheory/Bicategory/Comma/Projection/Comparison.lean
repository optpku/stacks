module

public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Lax
public import ReasLib.CategoryTheory.Bicategory.Comma.Projection.Endpoint

@[expose] public section

/-!
# Universal colax comma comparison

This leaf exposes the oplax comparison between the two endpoint projections of
a colax comma bicategory.
-/

universe wA vA uA wB vB uB wC vC uC

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace Bicategory

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

namespace ColaxComma

variable {F : A ⥤ᵖ C} {G : B ⥤ᵖ C}

section ComparisonImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/- Implementation boundary: coherence of the universal oplax comparison is stored only to build
comparison; its app and naturality cells are exposed semantically below. -/

/-- Naturality of the universal comma comparison with respect to comma 2-morphisms. -/
private theorem comparison_naturality_naturality {S T : ColaxComma F G}
    {f g : S ⟶ T} (η : f ⟶ g) :
    ((((fst F G).comp F).toLax.map₂ η) ▷ T.hom) ≫ g.cell =
      f.cell ≫
        (S.hom ◁ (((snd F G).comp G).toLax.map₂ η)) := sorry
/- Proof strategy: unfold the projection pseudofunctors and `comparison`; this is exactly the
stored compatibility equation `η.w`. -/

/-- Identity coherence of the universal comma comparison. -/
private theorem comparison_naturality_id (S : ColaxComma F G) :
    ((((fst F G).comp F).toLax.mapId S) ▷ S.hom) ≫
        ((𝟙 S : S ⟶ S).cell) =
      (λ_ S.hom).hom ≫ (ρ_ S.hom).inv ≫
        S.hom ◁ (((snd F G).comp G).toLax.mapId S) := sorry
/- Proof strategy: use the public identity-cell computation and the projection identity comparisons; unit coherence
identifies the two canonical pastings. -/

/-- Composition coherence of the universal comma comparison. -/
private theorem comparison_naturality_comp {S T U : ColaxComma F G}
    (f : S ⟶ T) (g : T ⟶ U) :
    ((((fst F G).comp F).toLax.mapComp f g) ▷ U.hom) ≫
        ((f ≫ g).cell) =
      (α_ _ _ _).hom ≫
        ((fst F G).comp F).toLax.map f ◁ g.cell ≫
          (α_ _ _ _).inv ≫ f.cell ▷
            ((snd F G).comp G).toLax.map g ≫
              (α_ _ _ _).hom ≫
                S.hom ◁ (((snd F G).comp G).toLax.mapComp f g) := sorry
/- Proof strategy: rewrite with `comp_cell f g` and both projection composition comparisons, then reassociate
using pseudofunctor composition coherence. -/

end Implementation

variable (F G) in
/-- The universal oplax comparison from `F` after the left projection to `G` after
the right projection.

Its component at `S` is `S.hom`, and its naturality cell at `f` is exactly `f.cell`.
Together with `fst` and `snd`, this is the canonical comma square carried by
`ColaxComma F G`. -/
def comparison : Lax.OplaxTrans
    (((fst F G).comp F).toLax)
    (((snd F G).comp G).toLax) where
  app := fun S ↦ S.hom
  naturality := fun f ↦ f.cell
  naturality_naturality := Implementation.comparison_naturality_naturality
  naturality_id := Implementation.comparison_naturality_id
  naturality_comp := Implementation.comparison_naturality_comp

/-- The universal oplax comparison has the structural comma arrow as its object component. -/
@[simp]
theorem comparison_app (S : ColaxComma F G) :
    (comparison F G).app S = S.hom := sorry
/- Proof strategy: unfold comparison and read its app field. -/

/-- The universal oplax comparison has the stored comma cell as its naturality component. -/
@[simp]
theorem comparison_naturality {S T : ColaxComma F G} (f : S ⟶ T) :
    (comparison F G).naturality f = f.cell := sorry
/- Proof strategy: unfold comparison and read its naturality field. -/

end ComparisonImplementation

end ColaxComma
end Bicategory
end CategoryTheory
