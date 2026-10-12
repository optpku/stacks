/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Comma.Basic.Data

@[expose] public section

/-!
# Colax comma bicategory assembly

This leaf assembles the explicit colax comma object, hom, and cell data into a
bicategory. Its coherence implementation remains private; `hom₂Mk` and `isoMk`
are the public constructors needed by mapping and lifting constructions.
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

section CoreImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- Compatibility of identity endpoint cells with a comma comparison cell. -/
private theorem hom₂Id_w {S T : ColaxComma F G} (f : Hom S T) :
    (F.map₂ (𝟙 f.left) ▷ T.hom) ≫ f.cell =
      f.cell ≫ (S.hom ◁ G.map₂ (𝟙 f.right)) := sorry
/- Proof strategy: unfold the endpoint action on identity `2`-cells, use the pseudofunctor
`map₂_id` laws, and normalize unitors and whiskerings by bicategory coherence. -/

/-- The identity `2`-morphism of a colax comma `1`-morphism. -/
private def hom₂Id {S T : ColaxComma F G} (f : Hom S T) : Hom₂ f f where
  left := 𝟙 f.left
  right := 𝟙 f.right
  w := hom₂Id_w f

/-- Compatibility of vertically composed endpoint cells with comma comparison cells. -/
private theorem hom₂Comp_w {S T : ColaxComma F G} {f g h : Hom S T}
    (η : Hom₂ f g) (θ : Hom₂ g h) :
    (F.map₂ (η.left ≫ θ.left) ▷ T.hom) ≫ h.cell =
      f.cell ≫ (S.hom ◁ G.map₂ (η.right ≫ θ.right)) := sorry
/- Proof strategy: rewrite both pseudofunctor images with `map₂_comp`, distribute whiskering over
vertical composition, and paste `η.w` with `θ.w` using interchange. -/

/-- Vertical composition of colax comma `2`-morphisms. -/
private def hom₂Comp {S T : ColaxComma F G} {f g h : Hom S T}
    (η : Hom₂ f g) (θ : Hom₂ g h) : Hom₂ f h where
  left := η.left ≫ θ.left
  right := η.right ≫ θ.right
  w := hom₂Comp_w η θ

/-- Left identity for vertical composition of colax comma `2`-morphisms. -/
private theorem hom₂_id_comp {S T : ColaxComma F G} {f g : Hom S T} (η : Hom₂ f g) :
    hom₂Comp (hom₂Id f) η = η := sorry
/- Proof strategy: apply `Hom₂.ext`; both endpoint components are ambient identity laws, while
the compatibility field is proof-irrelevant. -/

/-- Right identity for vertical composition of colax comma `2`-morphisms. -/
private theorem hom₂_comp_id {S T : ColaxComma F G} {f g : Hom S T} (η : Hom₂ f g) :
    hom₂Comp η (hom₂Id g) = η := sorry
/- Proof strategy: apply `Hom₂.ext`; reduce both endpoint components to ambient right-identity
laws and discard the propositional compatibility witness. -/

/-- Associativity of vertical composition of colax comma `2`-morphisms. -/
private theorem hom₂_assoc {S T : ColaxComma F G} {f g h k : Hom S T}
    (η : Hom₂ f g) (θ : Hom₂ g h) (μ : Hom₂ h k) :
    hom₂Comp (hom₂Comp η θ) μ = hom₂Comp η (hom₂Comp θ μ) := sorry
/- Proof strategy: apply `Hom₂.ext`; both endpoint equations are associativity in the
corresponding hom-category, and compatibility witnesses are propositions. -/

/-- The hom-category between two objects of a colax comma bicategory. -/
private instance homCategory (S T : ColaxComma F G) : Category (Hom S T) where
  Hom := Hom₂
  id := hom₂Id
  comp := hom₂Comp
  id_comp := hom₂_id_comp
  comp_id := hom₂_comp_id
  assoc := hom₂_assoc

/-- The comparison cell of the identity colax comma `1`-morphism. -/
private def idCell (S : ColaxComma F G) :
    F.map (𝟙 S.left) ≫ S.hom ⟶ S.hom ≫ G.map (𝟙 S.right) :=
  (F.mapId S.left).hom ▷ S.hom ≫
    (λ_ S.hom).hom ≫ (ρ_ S.hom).inv ≫
      S.hom ◁ (G.mapId S.right).inv

/-- The identity `1`-morphism in a colax comma bicategory. -/
private def id (S : ColaxComma F G) : Hom S S where
  left := 𝟙 S.left
  right := 𝟙 S.right
  cell := idCell S

/-- The comparison cell of a composite of colax comma `1`-morphisms. -/
private def compCell {S T U : ColaxComma F G} (f : Hom S T) (g : Hom T U) :
    F.map (f.left ≫ g.left) ≫ U.hom ⟶
      S.hom ≫ G.map (f.right ≫ g.right) :=
  (F.mapComp f.left g.left).hom ▷ U.hom ≫
    (α_ (F.map f.left) (F.map g.left) U.hom).hom ≫
      F.map f.left ◁ g.cell ≫
        (α_ (F.map f.left) T.hom (G.map g.right)).inv ≫
          f.cell ▷ G.map g.right ≫
            (α_ S.hom (G.map f.right) (G.map g.right)).hom ≫
              S.hom ◁ (G.mapComp f.right g.right).inv

/-- Horizontal composition of colax comma `1`-morphisms. -/
private def comp {S T U : ColaxComma F G} (f : Hom S T) (g : Hom T U) : Hom S U where
  left := f.left ≫ g.left
  right := f.right ≫ g.right
  cell := compCell f g

/-- The object-level category structure of a colax comma bicategory. -/
@[reducible]
private def categoryStruct : CategoryStruct (ColaxComma F G) where
  Hom := Hom
  id := id
  comp := comp

end Implementation

/-- The identity `2`-morphism in a colax comma hom-category. -/
def Hom₂.id {S T : ColaxComma F G} (f : Hom S T) : Hom₂ f f :=
  Implementation.hom₂Id f

/-- Vertical composition in a colax comma hom-category. -/
def Hom₂.comp {S T : ColaxComma F G} {f g h : Hom S T}
    (η : Hom₂ f g) (θ : Hom₂ g h) : Hom₂ f h :=
  Implementation.hom₂Comp η θ

/-- The identity `1`-morphism in a colax comma bicategory. -/
def Hom.id (S : ColaxComma F G) : Hom S S :=
  Implementation.id S

/-- Horizontal composition in a colax comma bicategory. -/
def Hom.comp {S T U : ColaxComma F G} (f : Hom S T) (g : Hom T U) : Hom S U :=
  Implementation.comp f g

/-- The section-local category-structure pin used while assembling the comma bicategory. -/
-- Local instance justification (defeq pin): fixes Hom, identity, and composition during bicategory assembly; a global competing CategoryStruct would overlap with the completed bicategory superclass.
local instance colaxCommaCategoryStruct : CategoryStruct (ColaxComma F G) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

/-- The section-local identification of bicategorical homs with the explicit comma hom-categories. -/
-- Local instance justification (defeq pin): identifies each displayed hom with the explicit Hom S T category during assembly; a global instance would overlap with the hom categories of the completed bicategory.
local instance colaxCommaHomCategory (S T : ColaxComma F G) : Category (S ⟶ T) :=
  inferInstanceAs (Category (Hom S T))

/-- Construct a colax comma `2`-morphism from endpoint cells and their compatibility. -/
@[stacks 003Q "colax comma 2-morphism constructor"]
def hom₂Mk {S T : ColaxComma F G} {f g : S ⟶ T}
    (left : f.left ⟶ g.left) (right : f.right ⟶ g.right)
    (w : (F.map₂ left ▷ T.hom) ≫ g.cell =
      f.cell ≫ (S.hom ◁ G.map₂ right)) : f ⟶ g where
  left := left
  right := right
  w := w

/-- Compatibility of the inverse endpoint cells in a colax comma isomorphism. -/
theorem isoMk_inv_w {S T : ColaxComma F G} {f g : S ⟶ T}
    (left : f.left ≅ g.left) (right : f.right ≅ g.right)
    (w : (F.map₂ left.hom ▷ T.hom) ≫ g.cell =
      f.cell ≫ (S.hom ◁ G.map₂ right.hom)) :
    (F.map₂ left.inv ▷ T.hom) ≫ f.cell =
      g.cell ≫ (S.hom ◁ G.map₂ right.inv) := sorry
/- Proof strategy: paste the given square with inverse endpoint cells, then cancel the `map₂`
images of the forward cells using pseudofunctoriality and inverse laws. -/

/-- The forward and inverse cells constructed from endpoint isomorphisms compose to
the identity on the source comma `1`-morphism. -/
theorem isoMk_hom_inv_id {S T : ColaxComma F G} {f g : S ⟶ T}
    (left : f.left ≅ g.left) (right : f.right ≅ g.right)
    (w : (F.map₂ left.hom ▷ T.hom) ≫ g.cell =
      f.cell ≫ (S.hom ◁ G.map₂ right.hom)) :
    hom₂Mk left.hom right.hom w ≫
      hom₂Mk left.inv right.inv (isoMk_inv_w left right w) = 𝟙 f := sorry
/- Proof strategy: use `Hom₂.ext`; the endpoint components reduce to `left.hom_inv_id` and
`right.hom_inv_id`. -/

/-- The inverse and forward cells constructed from endpoint isomorphisms compose to
the identity on the target comma `1`-morphism. -/
theorem isoMk_inv_hom_id {S T : ColaxComma F G} {f g : S ⟶ T}
    (left : f.left ≅ g.left) (right : f.right ≅ g.right)
    (w : (F.map₂ left.hom ▷ T.hom) ≫ g.cell =
      f.cell ≫ (S.hom ◁ G.map₂ right.hom)) :
    hom₂Mk left.inv right.inv (isoMk_inv_w left right w) ≫
      hom₂Mk left.hom right.hom w = 𝟙 g := sorry
/- Proof strategy: use `Hom₂.ext`; the endpoint components reduce to `left.inv_hom_id` and
`right.inv_hom_id`. -/

/-- Construct an isomorphism of colax comma `1`-morphisms from compatible endpoint
isomorphisms. -/
@[stacks 003Q "colax comma 2-isomorphism constructor"]
def isoMk {S T : ColaxComma F G} {f g : S ⟶ T}
    (left : f.left ≅ g.left) (right : f.right ≅ g.right)
    (w : (F.map₂ left.hom ▷ T.hom) ≫ g.cell =
      f.cell ≫ (S.hom ◁ G.map₂ right.hom)) : f ≅ g where
  hom := hom₂Mk left.hom right.hom w
  inv := hom₂Mk left.inv right.inv (isoMk_inv_w left right w)
  hom_inv_id := isoMk_hom_inv_id left right w
  inv_hom_id := isoMk_inv_hom_id left right w

namespace Implementation

/-- Compatibility of left whiskering with composite colax comma comparison cells. -/
private theorem whiskerLeft_w {S T U : ColaxComma F G} (f : S ⟶ T) {g h : T ⟶ U}
    (η : g ⟶ h) :
    (F.map₂ (f.left ◁ η.left) ▷ U.hom) ≫ (comp f h).cell =
      (comp f g).cell ≫ (S.hom ◁ G.map₂ (f.right ◁ η.right)) := sorry
/- Proof strategy: expand `compCell`, replace the central occurrence with `η.w`, and use
pseudofunctor left-whiskering coherence plus associator naturality. -/

/-- Left whiskering in the colax comma bicategory. -/
private def whiskerLeft {S T U : ColaxComma F G} (f : S ⟶ T) {g h : T ⟶ U}
    (η : g ⟶ h) : comp f g ⟶ comp f h :=
  hom₂Mk (f.left ◁ η.left) (f.right ◁ η.right) (whiskerLeft_w f η)

/-- Compatibility of right whiskering with composite colax comma comparison cells. -/
private theorem whiskerRight_w {S T U : ColaxComma F G} {f g : S ⟶ T}
    (η : f ⟶ g) (h : T ⟶ U) :
    (F.map₂ (η.left ▷ h.left) ▷ U.hom) ≫ (comp g h).cell =
      (comp f h).cell ≫ (S.hom ◁ G.map₂ (η.right ▷ h.right)) := sorry
/- Proof strategy: expand `compCell`, paste in `η.w`, and use pseudofunctor right-whiskering
coherence together with associator naturality and interchange. -/

/-- Right whiskering in the colax comma bicategory. -/
private def whiskerRight {S T U : ColaxComma F G} {f g : S ⟶ T}
    (η : f ⟶ g) (h : T ⟶ U) : comp f h ⟶ comp g h :=
  hom₂Mk (η.left ▷ h.left) (η.right ▷ h.right) (whiskerRight_w η h)

/-- Compatibility of the two ambient associators with colax comma comparison cells. -/
private theorem associator_w {R S T U : ColaxComma F G}
    (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U) :
    (F.map₂ (α_ f.left g.left h.left).hom ▷ U.hom) ≫
        (comp f (comp g h)).cell =
      (comp (comp f g) h).cell ≫
        (R.hom ◁ G.map₂ (α_ f.right g.right h.right).hom) := sorry
/- Proof strategy: expand both composite cells and normalize the pasting; endpoint pseudofunctor
associator axioms and the ambient pentagon identify the results. -/

/-- The associator in the colax comma bicategory. -/
private def associator {R S T U : ColaxComma F G}
    (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U) :
    comp (comp f g) h ≅ comp f (comp g h) :=
  isoMk (α_ f.left g.left h.left) (α_ f.right g.right h.right)
    (associator_w f g h)

/-- Compatibility of the two ambient left unitors with a colax comma comparison cell. -/
private theorem leftUnitor_w {S T : ColaxComma F G} (f : S ⟶ T) :
    (F.map₂ (λ_ f.left).hom ▷ T.hom) ≫ f.cell =
      (comp (id S) f).cell ≫ (S.hom ◁ G.map₂ (λ_ f.right).hom) := sorry
/- Proof strategy: unfold `idCell` and `compCell`, then use pseudofunctor left-unitor coherence and
the ambient triangle law. -/

/-- The left unitor in the colax comma bicategory. -/
private def leftUnitor {S T : ColaxComma F G} (f : S ⟶ T) : comp (id S) f ≅ f :=
  isoMk (λ_ f.left) (λ_ f.right) (leftUnitor_w f)

/-- Compatibility of the two ambient right unitors with a colax comma comparison cell. -/
private theorem rightUnitor_w {S T : ColaxComma F G} (f : S ⟶ T) :
    (F.map₂ (ρ_ f.left).hom ▷ T.hom) ≫ f.cell =
      (comp f (id T)).cell ≫ (S.hom ◁ G.map₂ (ρ_ f.right).hom) := sorry
/- Proof strategy: unfold `idCell` and `compCell`, apply pseudofunctor right-unitor coherence, and
normalize the remaining unitors and associators. -/

/-- The right unitor in the colax comma bicategory. -/
private def rightUnitor {S T : ColaxComma F G} (f : S ⟶ T) : comp f (id T) ≅ f :=
  isoMk (ρ_ f.left) (ρ_ f.right) (rightUnitor_w f)

/-- Left whiskering preserves identity `2`-morphisms. -/
private theorem whiskerLeft_id {S T U : ColaxComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    whiskerLeft f (𝟙 g) = 𝟙 (comp f g) := sorry
/- Proof strategy: apply `Hom₂.ext`; each endpoint is the ambient `whiskerLeft_id` law, and the
compatibility proof is irrelevant. -/

/-- Left whiskering preserves vertical composition. -/
private theorem whiskerLeft_comp {S T U : ColaxComma F G} (f : S ⟶ T)
    {g h k : T ⟶ U} (η : g ⟶ h) (θ : h ⟶ k) :
    whiskerLeft f (η ≫ θ) = whiskerLeft f η ≫ whiskerLeft f θ := sorry
/- Proof strategy: apply `Hom₂.ext`; use preservation of vertical composition by ambient left
whiskering on the left and right endpoints. -/

/-- Whiskering by an identity comma morphism is controlled by the left unitors. -/
private theorem id_whiskerLeft {S T : ColaxComma F G} {f g : S ⟶ T} (η : f ⟶ g) :
    whiskerLeft (id S) η =
      (leftUnitor f).hom ≫ η ≫ (leftUnitor g).inv := sorry
/- Proof strategy: apply `Hom₂.ext`; both endpoint equations are the ambient `id_whiskerLeft`
coherence with the corresponding unitors. -/

/-- Left whiskering by a composite is controlled by the comma associators. -/
private theorem comp_whiskerLeft {R S T U : ColaxComma F G} (f : R ⟶ S) (g : S ⟶ T)
    {h k : T ⟶ U} (η : h ⟶ k) :
    whiskerLeft (comp f g) η =
      (associator f g h).hom ≫ whiskerLeft f (whiskerLeft g η) ≫
        (associator f g k).inv := sorry
/- Proof strategy: apply `Hom₂.ext`; the endpoint components are the ambient `comp_whiskerLeft`
laws, conjugated by the endpoint associators. -/

/-- Right whiskering preserves identity `2`-morphisms. -/
private theorem id_whiskerRight {S T U : ColaxComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    whiskerRight (𝟙 f) g = 𝟙 (comp f g) := sorry
/- Proof strategy: apply `Hom₂.ext`; each endpoint reduces to the ambient identity preservation
law for right whiskering. -/

/-- Right whiskering preserves vertical composition. -/
private theorem comp_whiskerRight {S T U : ColaxComma F G} {f g h : S ⟶ T}
    (η : f ⟶ g) (θ : g ⟶ h) (k : T ⟶ U) :
    whiskerRight (η ≫ θ) k = whiskerRight η k ≫ whiskerRight θ k := sorry
/- Proof strategy: apply `Hom₂.ext`; use preservation of vertical composition by ambient right
whiskering at both endpoints. -/

/-- Whiskering on the right by an identity comma morphism is controlled by the right unitors. -/
private theorem whiskerRight_id {S T : ColaxComma F G} {f g : S ⟶ T} (η : f ⟶ g) :
    whiskerRight η (id T) =
      (rightUnitor f).hom ≫ η ≫ (rightUnitor g).inv := sorry
/- Proof strategy: apply `Hom₂.ext`; both endpoint equations are the ambient `whiskerRight_id`
coherence with right unitors. -/

/-- Right whiskering by a composite is controlled by the comma associators. -/
private theorem whiskerRight_comp {R S T U : ColaxComma F G} {f g : R ⟶ S}
    (η : f ⟶ g) (h : S ⟶ T) (k : T ⟶ U) :
    whiskerRight η (comp h k) =
      (associator f h k).inv ≫ whiskerRight (whiskerRight η h) k ≫
        (associator g h k).hom := sorry
/- Proof strategy: apply `Hom₂.ext`; each endpoint is the ambient `whiskerRight_comp` equation
controlled by associators. -/

/-- Left and right whiskering satisfy the associativity comparison. -/
private theorem whisker_assoc {R S T U : ColaxComma F G} (f : R ⟶ S)
    {g h : S ⟶ T} (η : g ⟶ h) (k : T ⟶ U) :
    whiskerRight (whiskerLeft f η) k =
      (associator f g k).hom ≫ whiskerLeft f (whiskerRight η k) ≫
        (associator f h k).inv := sorry
/- Proof strategy: apply `Hom₂.ext`; the left and right components are exactly the ambient
whiskering-associativity coherence equations. -/

/-- Left and right whiskering satisfy the exchange law. -/
private theorem whisker_exchange {S T U : ColaxComma F G} {f g : S ⟶ T}
    {h k : T ⟶ U} (η : f ⟶ g) (θ : h ⟶ k) :
    whiskerLeft f θ ≫ whiskerRight η k =
      whiskerRight η h ≫ whiskerLeft g θ := sorry
/- Proof strategy: apply `Hom₂.ext`; use the ambient interchange law independently on the two
endpoint `2`-morphisms. -/

/-- The colax comma associators satisfy the pentagon equation. -/
private theorem pentagon {Q R S T U : ColaxComma F G}
    (f : Q ⟶ R) (g : R ⟶ S) (h : S ⟶ T) (k : T ⟶ U) :
    whiskerRight (associator f g h).hom k ≫
        (associator f (comp g h) k).hom ≫
          whiskerLeft f (associator g h k).hom =
      (associator (comp f g) h k).hom ≫
        (associator f g (comp h k)).hom := sorry
/- Proof strategy: apply `Hom₂.ext`; each endpoint is the ambient bicategory pentagon, while
comma compatibility witnesses are proof-irrelevant. -/

/-- The colax comma associators and unitors satisfy the triangle equation. -/
private theorem triangle {S T U : ColaxComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    (associator f (id T) g).hom ≫ whiskerLeft f (leftUnitor g).hom =
      whiskerRight (rightUnitor f).hom g := sorry
/- Proof strategy: apply `Hom₂.ext`; the endpoint equations are the ambient triangle laws and the
compatibility fields are propositions. -/

end Implementation

/-- The bicategory structure on the colax comma construction. -/
@[stacks 003Q "colax comma bicategory"]
instance bicategory : Bicategory (ColaxComma F G) where
  toCategoryStruct := Implementation.categoryStruct
  homCategory _ _ := inferInstance
  whiskerLeft := Implementation.whiskerLeft
  whiskerRight := Implementation.whiskerRight
  associator := Implementation.associator
  leftUnitor := Implementation.leftUnitor
  rightUnitor := Implementation.rightUnitor
  whiskerLeft_id := Implementation.whiskerLeft_id
  whiskerLeft_comp := Implementation.whiskerLeft_comp
  id_whiskerLeft := Implementation.id_whiskerLeft
  comp_whiskerLeft := Implementation.comp_whiskerLeft
  id_whiskerRight := Implementation.id_whiskerRight
  comp_whiskerRight := Implementation.comp_whiskerRight
  whiskerRight_id := Implementation.whiskerRight_id
  whiskerRight_comp := Implementation.whiskerRight_comp
  whisker_assoc := Implementation.whisker_assoc
  whisker_exchange := Implementation.whisker_exchange
  pentagon := Implementation.pentagon
  triangle := Implementation.triangle

end CoreImplementation

end ColaxComma
end Bicategory
end CategoryTheory
