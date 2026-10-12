/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Chosen right internal Homs

The right-oriented convention represents `W ⊗ X ⟶ Y` by `W ⟶ hom(X, Y)`. This file owns the
bundled bifunctor and parametrized adjunction, their canonical maps, and the comparison between
two choices. Calculation and coherence statements live in focused downstream leaves.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory Opposite

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-
The right-oriented convention is
`Mor(W, hom(X, Y)) ≃ Mor(W ⊗ X, Y)`. Its reusable owner is data consisting of

* a bifunctor `hom : Cᵒᵖ ⥤ C ⥤ C`, and
* a parametrized adjunction `tensoringRight C ⊣₂ hom`.

This is deliberately not a class or a Prop wrapper: a category can carry several chosen
right internal-Hom structures, and the source immediately uses their computational data.
`RightInternalHom.uniqueIso` records that any two choices are canonically naturally isomorphic.

The opt-in notation `X ⟶[H]ᵣ Y` displays the bundled owner `H` explicitly. The final `ᵣ`
distinguishes it syntactically and visually from mathlib's left-oriented global notation
`X ⟶[C] Y`; users enable it with `open scoped CategoryTheory.RightInternalHom`.

Mathlib's `MonoidalClosed.internalHomAdjunction₂` has left adjoint `curriedTensor C`, hence
represents `Mor(X ⊗ W, Y)`, while this owner uses `tensoringRight C` and represents
`Mor(W ⊗ X, Y)`. The braided monoidal-closed bridge is provided by the opt-in leaf
`CategoryTheory.Monoidal.RightInternalHom.BraidedClosed`; no definitional identification with
`MonoidalClosed` is asserted by this base owner.
-/

/-- A chosen right internal-Hom structure on `C`. Its adjunction gives
`Mor(W, hom(X, Y)) ≃ Mor(W ⊗ X, Y)` naturally in `W`, `X`, and `Y`. -/
@[stacks 0GWJ "right internal-Hom data"]
structure RightInternalHom (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  /-- The right internal-Hom bifunctor, contravariant in its first argument. -/
  hom : Cᵒᵖ ⥤ C ⥤ C
  /-- The parametrized adjunction exhibiting `hom(X, -)` as right adjoint to `(-) ⊗ X`. -/
  adj₂ : tensoringRight C ⊣₂ hom

/- `H` is visibly a bundled right internal-Hom owner rather than the ambient category.
The trailing `ᵣ` keeps this syntax disjoint from mathlib's `X ⟶[C] Y`. -/
set_option quotPrecheck false in
scoped[CategoryTheory.RightInternalHom] notation X:arg " ⟶[" H "]ᵣ " Y:10 =>
  ((RightInternalHom.hom H).obj (op X)).obj Y

namespace RightInternalHom

open scoped CategoryTheory.RightInternalHom

section UniqueIsoImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The pointwise right-adjoint uniqueness isomorphisms are natural in the internal-Hom
parameter. -/
private theorem uniqueIso_naturality (H H' : RightInternalHom C)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    H.hom.map f ≫
        ((H.adj₂.adj (unop Y)).rightAdjointUniq (H'.adj₂.adj (unop Y))).hom =
      ((H.adj₂.adj (unop X)).rightAdjointUniq (H'.adj₂.adj (unop X))).hom ≫
        H'.hom.map f := by
  ext Z
  apply ((H'.adj₂.adj (unop Y)).homEquiv _ _).symm.injective
  simp only [NatTrans.comp_app]
  rw [Adjunction.homEquiv_naturality_left_symm]
  rw [Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
  have h' := H'.adj₂.homEquiv_symm_naturality_one f.unop
    (((H.adj₂.adj (unop X)).rightAdjointUniq
      (H'.adj₂.adj (unop X))).hom.app Z)
  simp only [ParametrizedAdjunction.homEquiv_eq,
    Adjunction.homEquiv_symm_rightAdjointUniq_hom_app] at h'
  simp only [op_unop, Quiver.Hom.op_unop] at h'
  rw [h']
  exact (NatTrans.congr_app (H.adj₂.whiskerLeft_map_counit f.unop) Z).symm

/-- Assemble the pointwise right-adjoint uniqueness isomorphisms into a natural isomorphism.
The component data is supplied by `Adjunction.rightAdjointUniq`; only naturality is deferred. -/
private noncomputable def uniqueIso (H H' : RightInternalHom C) : H.hom ≅ H'.hom :=
  NatIso.ofComponents
    (fun X => (H.adj₂.adj (unop X)).rightAdjointUniq (H'.adj₂.adj (unop X)))
    (fun f => uniqueIso_naturality H H' f)

end Implementation

/-- Two chosen right internal-Hom bifunctors are canonically naturally isomorphic, pointwise by
uniqueness of right adjoints. -/
@[stacks 0GWJ "right internal-Hom uniqueness"]
noncomputable def uniqueIso (H H' : RightInternalHom C) : H.hom ≅ H'.hom :=
  Implementation.uniqueIso H H'

/-- The canonical uniqueness isomorphism has the pointwise right-adjoint uniqueness isomorphism
as its component at `X`. -/
@[simp, stacks 0GWJ "right internal-Hom uniqueness component"]
theorem uniqueIso.app (H H' : RightInternalHom C) (X : C) :
    (H.uniqueIso H').app (op X) =
      (H.adj₂.adj X).rightAdjointUniq (H'.adj₂.adj X) := by
  rfl

end UniqueIsoImplementation

variable (H : RightInternalHom C)

/-- The adjunction bijection for the chosen right internal Hom:
`W ⊗ X ⟶ Y` is identified with `W ⟶ hom(X, Y)`. -/
@[stacks 0GWJ "right internal-Hom adjunction"]
def homEquiv (X W Y : C) :
    (W ⊗ X ⟶ Y) ≃ (W ⟶ (X ⟶[H]ᵣ Y)) :=
  H.adj₂.homEquiv

/-- Curry a morphism `W ⊗ X ⟶ Y` through the chosen right internal Hom. -/
@[stacks 0GWJ "right internal-Hom curry"]
def curry {X W Y : C} (f : W ⊗ X ⟶ Y) : W ⟶ (X ⟶[H]ᵣ Y) :=
  H.homEquiv X W Y f

/-- Uncurry a morphism `W ⟶ hom(X, Y)` through the chosen right internal Hom. -/
@[stacks 0GWJ "right internal-Hom uncurry"]
def uncurry {X W Y : C} (f : W ⟶ (X ⟶[H]ᵣ Y)) : W ⊗ X ⟶ Y :=
  (H.homEquiv X W Y).symm f

/-- Evaluation for the chosen right internal Hom, `hom(X, Y) ⊗ X ⟶ Y`. It is the counit of
`(-) ⊗ X ⊣ hom(X, -)` at `Y`. -/
@[stacks 0GWJ "right internal-Hom evaluation"]
def ev (X Y : C) : (X ⟶[H]ᵣ Y) ⊗ X ⟶ Y :=
  (H.adj₂.adj X).counit.app Y

/-- The internal-Hom identity of `X`, regarded as a map from the tensor unit to
`hom(X, X)`. Its uncurrying is the left unitor of `X`. -/
@[stacks 0GWJ "right internal-Hom identity"]
def id (X : C) : 𝟙_ C ⟶ (X ⟶[H]ᵣ X) :=
  H.curry (λ_ X).hom

/-- Composition for the chosen right internal Hom, `hom(Y, Z) ⊗ hom(X, Y) ⟶ hom(X, Z)`,
obtained by transposing double evaluation. -/
@[stacks 0GWJ "right internal-Hom composition"]
def comp (X Y Z : C) :
    ((Y ⟶[H]ᵣ Z) ⊗ (X ⟶[H]ᵣ Y)) ⟶ (X ⟶[H]ᵣ Z) :=
  H.adj₂.homEquiv
    ((α_ (Y ⟶[H]ᵣ Z) (X ⟶[H]ᵣ Y) X).hom ≫
      ((Y ⟶[H]ᵣ Z) ◁ H.ev X Y) ≫ H.ev Y Z)

/-- The canonical left-tensor morphism for the chosen right internal Hom,
`Z ⊗ hom(X, Y) ⟶ hom(X, Z ⊗ Y)`. -/
@[stacks 0GWJ "right internal-Hom left tensor map"]
def tensorLeft (X Y Z : C) :
    (Z ⊗ (X ⟶[H]ᵣ Y)) ⟶ (X ⟶[H]ᵣ (Z ⊗ Y)) :=
  H.adj₂.homEquiv
    ((α_ Z (X ⟶[H]ᵣ Y) X).hom ≫ (Z ◁ H.ev X Y))

/-- Coevaluation for the chosen right internal Hom, `Y ⟶ hom(X, Y ⊗ X)`. It is the unit of
`(-) ⊗ X ⊣ hom(X, -)` at `Y`. -/
@[stacks 0GWJ "right internal-Hom coevaluation"]
def coev (X Y : C) : Y ⟶ (X ⟶[H]ᵣ (Y ⊗ X)) :=
  (H.adj₂.adj X).unit.app Y

section Braided

variable [BraidedCategory C]

/-- In a braided monoidal category, the canonical composition transpose
`hom(Y, Z) ⊗ X ⟶ hom(hom(X, Y), Z)`. The construction only uses the braiding that interchanges
`X` and `hom(X, Y)`. -/
@[stacks 0GWJ "right internal-Hom composition transpose"]
def compTranspose (X Y Z : C) :
    ((Y ⟶[H]ᵣ Z) ⊗ X) ⟶ ((X ⟶[H]ᵣ Y) ⟶[H]ᵣ Z) :=
  H.adj₂.homEquiv
    ((α_ (Y ⟶[H]ᵣ Z) X (X ⟶[H]ᵣ Y)).hom ≫
      ((Y ⟶[H]ᵣ Z) ◁ (β_ X (X ⟶[H]ᵣ Y)).hom) ≫
      ((Y ⟶[H]ᵣ Z) ◁ H.ev X Y) ≫ H.ev Y Z)

end Braided

end RightInternalHom

end CategoryTheory
