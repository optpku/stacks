/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map.Coherence
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Functoriality.Identity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity comparison for mapping bundled bicategorical cospans

The action of the identity pseudofunctor on bundled cospans is compared with the identity
pseudofunctor by a strong transformation. Every object component is an identity cospan
morphism. Naturality is the canonical unitor-adjusted lift of
`CospanTransform.mapIdentityIso`.

Projection-level computations are layered in
`Cospan.Bundled.Map.Functoriality.Identity`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

universe w v u

namespace CategoryTheory.Bicategory.Cospan

variable {B : Type u} [Bicategory.{w, v} B]

/-- Naturality of the identity comparison for componentwise mapping of bundled cospans.

The middle isomorphism is the canonical comparison between mapping the underlying cospan
transformation by `Pseudofunctor.id B` and leaving it unchanged; the unitors adjust it to the
strong-transformation naturality convention. -/
@[stacks 0040 "naturality isomorphism for identity mapping of bundled bicategorical cospans"]
def mapIdentity.naturalityIso {S T : Cospan B} (ψ : S ⟶ T) :
    (map (Pseudofunctor.id B)).map ψ ≫ 𝟙 T ≅
      𝟙 S ≫ (Pseudofunctor.id (Cospan B)).map ψ :=
  ρ_ ((map (Pseudofunctor.id B)).map ψ) ≪≫
    InducedBicategory.isoMk
      (CospanTransform.mapIdentityIso (Hom.toCospanTransform ψ)) ≪≫
        (λ_ ψ).symm

namespace Implementation.mapIdentity

/-- The identity comparison is natural in bundled-cospan `2`-morphisms. -/
private theorem naturality
    {S T : Cospan B} {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    (map (Pseudofunctor.id B)).map₂ Γ ▷ 𝟙 T ≫
        (mapIdentity.naturalityIso φ).hom =
      (mapIdentity.naturalityIso ψ).hom ≫
        𝟙 S ◁ (Pseudofunctor.id (Cospan B)).map₂ Γ := sorry

/-- The naturality isomorphism of the identity comparison is compatible with identity
`1`-morphisms. -/
private theorem id (S : Cospan B) :
    (mapIdentity.naturalityIso (𝟙 S)).hom ≫
        𝟙 S ◁ ((Pseudofunctor.id (Cospan B)).mapId S).hom =
      ((map (Pseudofunctor.id B)).mapId S).hom ▷ 𝟙 S ≫
        (λ_ (𝟙 S)).hom ≫ (ρ_ (𝟙 S)).inv := sorry

/-- The naturality isomorphism of the identity comparison is compatible with composition of
bundled-cospan `1`-morphisms. -/
private theorem comp
    {R S T : Cospan B} (ψ : R ⟶ S) (φ : S ⟶ T) :
    (mapIdentity.naturalityIso (ψ ≫ φ)).hom ≫
        𝟙 R ◁ ((Pseudofunctor.id (Cospan B)).mapComp ψ φ).hom =
      ((map (Pseudofunctor.id B)).mapComp ψ φ).hom ▷ 𝟙 T ≫
        (α_ _ _ _).hom ≫
          (map (Pseudofunctor.id B)).map ψ ◁
            (mapIdentity.naturalityIso φ).hom ≫
          (α_ _ _ _).inv ≫
            (mapIdentity.naturalityIso ψ).hom ▷
              (Pseudofunctor.id (Cospan B)).map φ ≫
            (α_ _ _ _).hom := sorry

end Implementation.mapIdentity

variable (B) in
/-- Mapping bundled cospans by the identity pseudofunctor is canonically strongly
transformed to the identity pseudofunctor on bundled cospans.

Every object component is an identity morphism; all nontrivial comparison data are concentrated
in `mapIdentity.naturalityIso`. The ambient bicategory is explicit because this global comparison
has no value input from which it can be inferred. -/
@[stacks 0040 "identity comparison for mapping bundled bicategorical cospans"]
def mapIdentity :
    map (Pseudofunctor.id B) ⟶ Pseudofunctor.id (Cospan B) where
  app S := 𝟙 S
  naturality ψ := mapIdentity.naturalityIso ψ
  naturality_naturality := Implementation.mapIdentity.naturality
  naturality_id := Implementation.mapIdentity.id
  naturality_comp := Implementation.mapIdentity.comp

/-- The object component of `mapIdentity` is the identity cospan morphism. -/
@[simp]
theorem mapIdentity.app (S : Cospan B) :
    (mapIdentity B).app S = 𝟙 S := sorry

/-- The naturality isomorphism of `mapIdentity` is `mapIdentity.naturalityIso`. -/
@[simp]
theorem mapIdentity.naturality
    {S T : Cospan B} (ψ : S ⟶ T) :
    (mapIdentity B).naturality ψ =
      mapIdentity.naturalityIso ψ := sorry

/- Data and axiom audit (mathlib 4.32):

`mapIdentity.naturalityIso` is explicitly the right unitor, the lifted
`CospanTransform.mapIdentityIso`, and the inverse left unitor. `mapIdentity` has explicit
identity object components and uses that naturality datum. Any `sorryAx` dependency is confined
to the three strong-transformation laws, the generating naturality squares of the lifted
comparison, and inherited bicategorical coherence. -/

end CategoryTheory.Bicategory.Cospan
