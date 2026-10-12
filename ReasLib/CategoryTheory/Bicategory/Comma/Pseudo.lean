/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Lax
public import ReasLib.CategoryTheory.Bicategory.LocalProperties
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Lift
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.LocalProperties
public import ReasLib.CategoryTheory.Bicategory.Comma.Projection.Endpoint

@[expose] public section

/-!
# Pseudo comma bicategories

This leaf selects the locally full bicategory of colax comma morphisms whose
comparison cells are invertible and exposes its projections and strong comparison.
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

/-- The hom property selecting colax comma `1`-morphisms whose comparison cell
is invertible. These are the tight morphisms of the comma enhancement. -/
def pseudoHomProperty (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) :
    HomProperty (fun S : ColaxComma F G ↦ S) :=
  fun _ _ f ↦ IsIso f.cell

namespace pseudoHomProperty

/-- Identity comma morphisms have invertible comparison cells. -/
theorem id_mem (S : ColaxComma F G) :
    pseudoHomProperty F G S S (𝟙 S) := sorry
/- Proof strategy: unfold `pseudoHomProperty` and use the public identity-cell computation; every factor is an isomorphism supplied
by a pseudofunctor comparison or bicategory unitor. -/

/-- Composites of comma morphisms with invertible comparison cells again have
invertible comparison cells. -/
theorem comp_mem {S T U : ColaxComma F G} {f : S ⟶ T} {g : T ⟶ U}
    (hf : pseudoHomProperty F G S T f)
    (hg : pseudoHomProperty F G T U g) :
    pseudoHomProperty F G S U (f ≫ g) := sorry
/- Proof strategy: unfold `pseudoHomProperty` and use the canonical composite-cell pasting; combine `hf` and `hg` with
isomorphism instances for map comparisons, associators, and whiskerings. -/

/-- Invertible comma comparisons form a multiplicative hom property. -/
instance isMultiplicative : (pseudoHomProperty F G).IsMultiplicative where
  id_mem := id_mem
  comp_mem := comp_mem

/-- Invertibility of comma comparison cells is invariant under isomorphisms of comma
`1`-morphisms, uniformly in the two comma objects. -/
instance isClosedUnderIsomorphisms :
    (pseudoHomProperty F G).IsClosedUnderIsomorphisms := sorry
/- Proof strategy: transport the `IsIso` comparison-cell witness across the ambient hom-category
isomorphism and use the inverse isomorphism for the converse direction. -/


end pseudoHomProperty

end ColaxComma

/-- The pseudo comma bicategory of `F : A ⥤ᵖ C` and `G : B ⥤ᵖ C`.

It has all colax comma objects and only those `1`-morphisms whose structural
comparison cell is invertible. All compatible `2`-morphisms are retained. Thus
it is the locally full tight part of `ColaxComma F G` selected by invertible comparison cells,
rather than a second hand-written bicategory. -/
def PseudoComma (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) :=
  LocallyInducedBicategory (ColaxComma F G)
    (fun S : ColaxComma F G ↦ S) (ColaxComma.pseudoHomProperty F G)

namespace PseudoComma

variable {F : A ⥤ᵖ C} {G : B ⥤ᵖ C}

/-- The bicategory structure on the locally full pseudo comma specialization. -/
instance bicategory : Bicategory (PseudoComma F G) :=
  inferInstanceAs (Bicategory (LocallyInducedBicategory (ColaxComma F G)
    (fun S : ColaxComma F G ↦ S) (ColaxComma.pseudoHomProperty F G)))

/-- Pseudo comma bicategories inherit local groupoidality from both endpoint bicategories. -/
instance locallyGroupoid [IsLocallyGroupoid A] [IsLocallyGroupoid B] :
    IsLocallyGroupoid (PseudoComma F G) :=
  inferInstanceAs (IsLocallyGroupoid (LocallyInducedBicategory (ColaxComma F G)
    (fun S : ColaxComma F G ↦ S) (ColaxComma.pseudoHomProperty F G)))

/-- The map between the left endpoints of a pseudo comma `1`-morphism. -/
abbrev left {S T : PseudoComma F G} (f : S ⟶ T) : S.left ⟶ T.left :=
  f.obj.left

/-- The map between the right endpoints of a pseudo comma `1`-morphism. -/
abbrev right {S T : PseudoComma F G} (f : S ⟶ T) : S.right ⟶ T.right :=
  f.obj.right

/-- The comparison cell of a pseudo comma `1`-morphism. -/
abbrev cell {S T : PseudoComma F G} (f : S ⟶ T) :
    F.map (left f) ≫ T.hom ⟶ S.hom ≫ G.map (right f) :=
  f.obj.cell

/-- The comparison cell of a pseudo comma `1`-morphism is invertible. -/
instance cellIsIso {S T : PseudoComma F G} (f : S ⟶ T) : IsIso (cell f) :=
  f.property

/-- The structural comparison carried by a pseudo comma `1`-morphism. -/
noncomputable def cellIso {S T : PseudoComma F G} (f : S ⟶ T) :
    F.map (left f) ≫ T.hom ≅ S.hom ≫ G.map (right f) :=
  asIso (cell f)

/-- Construct a pseudo comma `1`-morphism from endpoint maps and an invertible
comparison cell. -/
def homMk {S T : PseudoComma F G}
    (fLeft : ColaxComma.left S ⟶ ColaxComma.left T)
    (fRight : ColaxComma.right S ⟶ ColaxComma.right T)
    (comparison : F.map fLeft ≫ ColaxComma.hom T ≅
      ColaxComma.hom S ≫ G.map fRight) : S ⟶ T :=
  LocallyInducedBicategory.mkHom
    ({ left := fLeft, right := fRight, cell := comparison.hom } :
      ColaxComma.Hom S T)
    comparison.isIso_hom

/-- The left endpoint map of a pseudo comma morphism constructed by `homMk` is the
supplied left endpoint map. -/
@[simp]
theorem homMk_left {S T : PseudoComma F G}
    (fLeft : ColaxComma.left S ⟶ ColaxComma.left T)
    (fRight : ColaxComma.right S ⟶ ColaxComma.right T)
    (comparison : F.map fLeft ≫ ColaxComma.hom T ≅
      ColaxComma.hom S ≫ G.map fRight) :
    left (homMk fLeft fRight comparison) = fLeft := sorry

/-- The right endpoint map of a pseudo comma morphism constructed by `homMk` is the
supplied right endpoint map. -/
@[simp]
theorem homMk_right {S T : PseudoComma F G}
    (fLeft : ColaxComma.left S ⟶ ColaxComma.left T)
    (fRight : ColaxComma.right S ⟶ ColaxComma.right T)
    (comparison : F.map fLeft ≫ ColaxComma.hom T ≅
      ColaxComma.hom S ≫ G.map fRight) :
    right (homMk fLeft fRight comparison) = fRight := sorry

/-- The comparison cell of a pseudo comma morphism constructed by `homMk` is the forward
cell of the supplied isomorphism. -/
@[simp]
theorem homMk_cell {S T : PseudoComma F G}
    (fLeft : ColaxComma.left S ⟶ ColaxComma.left T)
    (fRight : ColaxComma.right S ⟶ ColaxComma.right T)
    (comparison : F.map fLeft ≫ ColaxComma.hom T ≅
      ColaxComma.hom S ≫ G.map fRight) :
    cell (homMk fLeft fRight comparison) = comparison.hom := sorry

/-- The forward cell of the selected comparison isomorphism of `homMk` is the forward cell
of the supplied isomorphism. -/
@[simp]
theorem homMk_cellIso_hom {S T : PseudoComma F G}
    (fLeft : ColaxComma.left S ⟶ ColaxComma.left T)
    (fRight : ColaxComma.right S ⟶ ColaxComma.right T)
    (comparison : F.map fLeft ≫ ColaxComma.hom T ≅
      ColaxComma.hom S ≫ G.map fRight) :
    (cellIso (homMk fLeft fRight comparison)).hom = comparison.hom := sorry

/-- The inverse cell of the selected comparison isomorphism of `homMk` is the inverse cell
of the supplied isomorphism. -/
@[simp]
theorem homMk_cellIso_inv {S T : PseudoComma F G}
    (fLeft : ColaxComma.left S ⟶ ColaxComma.left T)
    (fRight : ColaxComma.right S ⟶ ColaxComma.right T)
    (comparison : F.map fLeft ≫ ColaxComma.hom T ≅
      ColaxComma.hom S ≫ G.map fRight) :
    (cellIso (homMk fLeft fRight comparison)).inv = comparison.inv := sorry

/-- The ambient `2`-morphism on the left endpoint of a pseudo comma `2`-morphism. -/
abbrev left₂ {S T : PseudoComma F G} {f g : S ⟶ T} (η : f ⟶ g) :
    left f ⟶ left g :=
  η.hom.left

/-- The ambient `2`-morphism on the right endpoint of a pseudo comma `2`-morphism. -/
abbrev right₂ {S T : PseudoComma F G} {f g : S ⟶ T} (η : f ⟶ g) :
    right f ⟶ right g :=
  η.hom.right

/-- Construct a pseudo comma `2`-morphism from compatible cells on its two endpoint maps.

The selected invertibility condition constrains only `1`-morphisms, so this is the direct
locally-full lift of a `ColaxComma.Hom₂`. -/
def hom₂Mk {S T : PseudoComma F G} {f g : S ⟶ T}
    (leftCell : left f ⟶ left g) (rightCell : right f ⟶ right g)
    (w : (F.map₂ leftCell ▷ T.hom) ≫ cell g =
      cell f ≫ (S.hom ◁ G.map₂ rightCell)) :
    f ⟶ g :=
  ObjectProperty.homMk
    ({ left := leftCell, right := rightCell, w } : ColaxComma.Hom₂ f.obj g.obj)

/-- The left endpoint cell of a pseudo comma `2`-morphism constructed by `hom₂Mk` is the
supplied left cell. -/
@[simp]
theorem hom₂Mk_left₂ {S T : PseudoComma F G} {f g : S ⟶ T}
    (leftCell : left f ⟶ left g) (rightCell : right f ⟶ right g)
    (w : (F.map₂ leftCell ▷ T.hom) ≫ cell g =
      cell f ≫ (S.hom ◁ G.map₂ rightCell)) :
    left₂ (hom₂Mk leftCell rightCell w) = leftCell := sorry

/-- The right endpoint cell of a pseudo comma `2`-morphism constructed by `hom₂Mk` is the
supplied right cell. -/
@[simp]
theorem hom₂Mk_right₂ {S T : PseudoComma F G} {f g : S ⟶ T}
    (leftCell : left f ⟶ left g) (rightCell : right f ⟶ right g)
    (w : (F.map₂ leftCell ▷ T.hom) ≫ cell g =
      cell f ≫ (S.hom ◁ G.map₂ rightCell)) :
    right₂ (hom₂Mk leftCell rightCell w) = rightCell := sorry

/-- Every pseudo comma `2`-morphism satisfies the compatibility equation of its endpoint
cells with the two structural comparison cells. -/
theorem map₂_cell {S T : PseudoComma F G} {f g : S ⟶ T} (η : f ⟶ g) :
    (F.map₂ (left₂ η) ▷ T.hom) ≫ cell g =
      cell f ≫ (S.hom ◁ G.map₂ (right₂ η)) := sorry

/-- Pseudo comma `2`-morphisms are determined by their two endpoint cells. -/
@[ext]
theorem hom₂_ext {S T : PseudoComma F G} {f g : S ⟶ T} {η θ : f ⟶ g}
    (hleft : left₂ η = left₂ θ) (hright : right₂ η = right₂ θ) :
    η = θ := sorry

/-- Reconstructing a pseudo comma `2`-morphism from its endpoint cells and compatibility
equation recovers the original `2`-morphism. -/
@[simp]
theorem hom₂Mk_components {S T : PseudoComma F G} {f g : S ⟶ T} (η : f ⟶ g) :
    hom₂Mk (left₂ η) (right₂ η) (map₂_cell η) = η := sorry

variable (F G) in
/-- The canonical inclusion of the pseudo comma bicategory into the colax comma
bicategory.

The two legs are explicit because this strict pseudofunctor has no value input
from which Lean can recover them. -/
def ι : StrictPseudofunctor (PseudoComma F G) (ColaxComma F G) :=
  LocallyInducedBicategory.forget (ColaxComma F G)
    (fun S : ColaxComma F G ↦ S) (ColaxComma.pseudoHomProperty F G)

/-- The pseudo-comma inclusion leaves objects unchanged. -/
@[simp]
theorem ι_obj (S : PseudoComma F G) :
    (ι F G).obj S = S := sorry

/-- The pseudo-comma inclusion forgets only the invertibility certificate on a `1`-morphism. -/
@[simp]
theorem ι_map {S T : PseudoComma F G} (f : S ⟶ T) :
    (ι F G).map f = f.obj := sorry

/-- The pseudo-comma inclusion forgets only the selected-hom wrapper on a `2`-morphism. -/
@[simp]
theorem ι_map₂ {S T : PseudoComma F G} {f g : S ⟶ T} (η : f ⟶ g) :
    (ι F G).map₂ η = η.hom := sorry

variable (F G) in
/-- The left projection from the pseudo comma bicategory.

The two legs are explicit because this pseudofunctor has no value input from
which Lean can recover them. -/
def fst : PseudoComma F G ⥤ᵖ A :=
  (ι F G).toPseudofunctor.comp (ColaxComma.fst F G)

/-- The left pseudo-comma projection returns the left endpoint object. -/
@[simp]
theorem fst_obj (S : PseudoComma F G) :
    (fst F G).obj S = ColaxComma.left S := sorry

/-- The left pseudo-comma projection returns the left endpoint map. -/
@[simp]
theorem fst_map {S T : PseudoComma F G} (f : S ⟶ T) :
    (fst F G).map f = left f := sorry

/-- The left pseudo-comma projection returns the left endpoint cell. -/
@[simp]
theorem fst_map₂ {S T : PseudoComma F G} {f g : S ⟶ T} (η : f ⟶ g) :
    (fst F G).map₂ η = left₂ η := sorry

variable (F G) in
/-- The right projection from the pseudo comma bicategory.

The two legs are explicit because this pseudofunctor has no value input from
which Lean can recover them. -/
def snd : PseudoComma F G ⥤ᵖ B :=
  (ι F G).toPseudofunctor.comp (ColaxComma.snd F G)

/-- The right pseudo-comma projection returns the right endpoint object. -/
@[simp]
theorem snd_obj (S : PseudoComma F G) :
    (snd F G).obj S = ColaxComma.right S := sorry

/-- The right pseudo-comma projection returns the right endpoint map. -/
@[simp]
theorem snd_map {S T : PseudoComma F G} (f : S ⟶ T) :
    (snd F G).map f = right f := sorry

/-- The right pseudo-comma projection returns the right endpoint cell. -/
@[simp]
theorem snd_map₂ {S T : PseudoComma F G} {f g : S ⟶ T} (η : f ⟶ g) :
    (snd F G).map₂ η = right₂ η := sorry

section ComparisonImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/- Implementation boundary: strong-comparison coherence is private; the public comparison exposes
its component and generating naturality isomorphism through semantic simp lemmas. -/

/-- Naturality in 2-morphisms of the canonical strong pseudo comma comparison. -/
private theorem comparison_naturality_naturality {S T : PseudoComma F G}
    {f g : S ⟶ T} (η : f ⟶ g) :
    (cellIso f).inv ≫ ((fst F G).comp F).toLax.map₂ η ▷ T.hom =
      S.hom ◁ ((snd F G).comp G).toLax.map₂ η ≫ (cellIso g).inv := sorry
/- Proof strategy: cancel the invertible structural cells in the ambient comma compatibility
equation, reversing the colax orientation into the displayed strong one. -/

/-- Identity coherence of the canonical strong pseudo comma comparison. -/
private theorem comparison_naturality_id (S : PseudoComma F G) :
    S.hom ◁ ((snd F G).comp G).toLax.mapId S ≫ (cellIso (𝟙 S)).inv =
      (ρ_ S.hom).hom ≫ (λ_ S.hom).inv ≫
        ((fst F G).comp F).toLax.mapId S ▷ S.hom := sorry
/- Proof strategy: specialize ambient identity coherence and invert its selected comparison cell;
unit coherence gives the strong identity equation. -/

/-- Composition coherence of the canonical strong pseudo comma comparison. -/
private theorem comparison_naturality_comp {S T U : PseudoComma F G}
    (f : S ⟶ T) (g : T ⟶ U) :
    S.hom ◁ ((snd F G).comp G).toLax.mapComp f g ≫ (cellIso (f ≫ g)).inv =
      (α_ _ _ _).inv ≫ (cellIso f).inv ▷
          ((snd F G).comp G).toLax.map g ≫
        (α_ _ _ _).hom ≫ ((fst F G).comp F).toLax.map f ◁ (cellIso g).inv ≫
          (α_ _ _ _).inv ≫
            (((fst F G).comp F).toLax.mapComp f g) ▷ U.hom := sorry
/- Proof strategy: invert the ambient composite pasting, use the two selected cell isomorphisms,
and normalize the reversed order by associator naturality. -/

end Implementation

variable (F G) in
/-- The canonical strong comparison from `F` after the left projection to `G`
after the right projection.

Its component at `S` is the structural map `S.hom`; its strong naturality
isomorphism at `f` is the inverse of the selected comma comparison. This is the
pseudonatural square that distinguishes `PseudoComma` from its colax ambient
bicategory. -/
noncomputable def comparison : Lax.StrongTrans
    (((fst F G).comp F).toLax)
    (((snd F G).comp G).toLax) where
  app := fun S ↦ S.hom
  naturality := fun f ↦ (cellIso f).symm
  naturality_naturality := Implementation.comparison_naturality_naturality
  naturality_id := Implementation.comparison_naturality_id
  naturality_comp := Implementation.comparison_naturality_comp

/-- The canonical strong pseudo comma comparison has the structural arrow as its object component. -/
@[simp]
theorem comparison_app (S : PseudoComma F G) :
    (comparison F G).app S = S.hom := sorry
/- Proof strategy: unfold comparison and read its app field. -/

/-- The canonical strong pseudo comma comparison uses the inverse selected comma cell on each
1-morphism. -/
@[simp]
theorem comparison_naturality {S T : PseudoComma F G} (f : S ⟶ T) :
    (comparison F G).naturality f = (cellIso f).symm := sorry
/- Proof strategy: unfold comparison and read its strong naturality field. -/

end ComparisonImplementation

/-- If the target bicategory is locally groupoidal, every colax comparison cell
is invertible, so the pseudo-to-colax inclusion induces equivalences on all hom-categories. -/
instance ιIsLocallyEquivalence [IsLocallyGroupoid C] :
    ((ι F G).toPseudofunctor).IsLocallyEquivalence := sorry
/- Proof strategy: local groupoidality of `C` makes every ambient comparison invertible, so every
colax morphism lifts canonically; `2`-morphisms are unchanged. -/

end PseudoComma

end Bicategory

end CategoryTheory
