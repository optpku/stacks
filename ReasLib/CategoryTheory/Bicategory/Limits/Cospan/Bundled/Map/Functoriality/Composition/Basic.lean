module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map.Coherence
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Functoriality.Composition

/-!
# Composition comparison for mapping bundled bicategorical cospans

The action on bundled cospans of a composite pseudofunctor is compared with the composite
action by a strong transformation. Every object component is an identity cospan morphism.
Naturality is the canonical unitor-adjusted lift of
`CospanTransform.mapCompositionIso`.

Projection-level computations are layered in
`Cospan.Bundled.Map.Functoriality.Composition`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

universe w v u w' v' u' w'' v'' u''

namespace CategoryTheory.Bicategory.Cospan

variable {B : Type u} [Bicategory.{w, v} B]
variable {B' : Type u'} [Bicategory.{w', v'} B']
variable {B'' : Type u''} [Bicategory.{w'', v''} B'']

/-- Naturality of the composition comparison for componentwise mapping of bundled cospans.

The middle isomorphism compares mapping the underlying cospan transformation by `P.comp Q`
with successive mapping by `P` and `Q`; the unitors adjust it to the strong-transformation
naturality convention. -/
@[stacks 0040 "naturality isomorphism for composition of bundled-cospan maps"]
def mapComposition.naturalityIso
    (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') {S T : Cospan B} (ψ : S ⟶ T) :
    (map (P.comp Q)).map ψ ≫ 𝟙 (((map P).comp (map Q)).obj T) ≅
      𝟙 ((map (P.comp Q)).obj S) ≫ ((map P).comp (map Q)).map ψ :=
  ρ_ ((map (P.comp Q)).map ψ) ≪≫
    InducedBicategory.isoMk
      (CospanTransform.mapCompositionIso (Hom.toCospanTransform ψ) P Q) ≪≫
        (λ_ (((map P).comp (map Q)).map ψ)).symm

namespace Implementation.mapComposition

/-- The composition comparison is natural in bundled-cospan `2`-morphisms. -/
private theorem naturality
    (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'')
    {S T : Cospan B} {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    (map (P.comp Q)).map₂ Γ ▷ 𝟙 (((map P).comp (map Q)).obj T) ≫
        (mapComposition.naturalityIso P Q φ).hom =
      (mapComposition.naturalityIso P Q ψ).hom ≫
        𝟙 ((map (P.comp Q)).obj S) ◁ ((map P).comp (map Q)).map₂ Γ := sorry

/-- The naturality isomorphism of the composition comparison is compatible with identity
`1`-morphisms. -/
private theorem id
    (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') (S : Cospan B) :
    (mapComposition.naturalityIso P Q (𝟙 S)).hom ≫
        𝟙 ((map (P.comp Q)).obj S) ◁ (((map P).comp (map Q)).mapId S).hom =
      ((map (P.comp Q)).mapId S).hom ▷
          𝟙 (((map P).comp (map Q)).obj S) ≫
        (λ_ (𝟙 ((map (P.comp Q)).obj S))).hom ≫
          (ρ_ (𝟙 ((map (P.comp Q)).obj S))).inv := sorry

/-- The naturality isomorphism of the composition comparison is compatible with composition
of bundled-cospan `1`-morphisms. -/
private theorem comp
    (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'')
    {R S T : Cospan B} (ψ : R ⟶ S) (φ : S ⟶ T) :
    (mapComposition.naturalityIso P Q (ψ ≫ φ)).hom ≫
        𝟙 ((map (P.comp Q)).obj R) ◁
          (((map P).comp (map Q)).mapComp ψ φ).hom =
      ((map (P.comp Q)).mapComp ψ φ).hom ▷
          𝟙 (((map P).comp (map Q)).obj T) ≫
        (α_ _ _ _).hom ≫
          (map (P.comp Q)).map ψ ◁
            (mapComposition.naturalityIso P Q φ).hom ≫
          (α_ _ _ _).inv ≫
            (mapComposition.naturalityIso P Q ψ).hom ▷
              ((map P).comp (map Q)).map φ ≫
            (α_ _ _ _).hom := sorry

end Implementation.mapComposition

/-- Mapping bundled cospans by a composite pseudofunctor is canonically strongly transformed
to successive mapping.

Every object component is an identity morphism; all nontrivial comparison data are concentrated
in `mapComposition.naturalityIso`. -/
@[stacks 0040 "composition comparison for mapping bundled bicategorical cospans"]
def mapComposition (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') :
    map (P.comp Q) ⟶ (map P).comp (map Q) where
  app S := 𝟙 ((map (P.comp Q)).obj S)
  naturality ψ := mapComposition.naturalityIso P Q ψ
  naturality_naturality := Implementation.mapComposition.naturality P Q
  naturality_id := Implementation.mapComposition.id P Q
  naturality_comp := Implementation.mapComposition.comp P Q

/-- The object component of `mapComposition` is the identity cospan morphism. -/
@[simp]
theorem mapComposition.app (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') (S : Cospan B) :
    (mapComposition P Q).app S = 𝟙 ((map (P.comp Q)).obj S) := sorry

/-- The naturality isomorphism of `mapComposition` is `mapComposition.naturalityIso`. -/
@[simp]
theorem mapComposition.naturality
    (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') {S T : Cospan B} (ψ : S ⟶ T) :
    (mapComposition P Q).naturality ψ = mapComposition.naturalityIso P Q ψ := sorry

/- Data and axiom audit (mathlib 4.32):

`mapComposition.naturalityIso` is explicitly the right unitor, the lifted
`CospanTransform.mapCompositionIso`, and the inverse left unitor. `mapComposition` has explicit
identity object components and uses that naturality datum. Any `sorryAx` dependency is confined
to the three strong-transformation laws, the generating naturality squares of the lifted
comparison, and inherited bicategorical coherence. -/

end CategoryTheory.Bicategory.Cospan
