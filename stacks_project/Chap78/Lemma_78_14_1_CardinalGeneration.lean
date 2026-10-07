module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Subobject.Lattice
public import stacks_project.Chap78.Lemma_78_14_1_Crystal

/-!
# Cardinal generation of crystals in quasi-coherent modules

On a pre-relation diagram of schemes with flat transition maps, every crystal in
quasi-coherent modules is the directed colimit of its `κ`-generated submodules for a
cardinal `κ` depending only on the diagram.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.RelDiagram

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelDiagram.Crystal

/-- A family of quasi-coherent subsheaves is a submodule of a crystal when each comparison
isomorphism identifies the pullback of the target subsheaf with the source subsheaf. -/
def IsCompatible {X : RelDiagram.{u}} (F : Crystal X)
    (B : (i : X.index) → Subobject (F.obj i)) : Prop :=
  ∀ φ : X.arrow,
    ∃ e : (QCoh.pullback (X.map φ)).obj (B (X.dst φ) : QCoh (X.obj (X.dst φ))) ≅
        (B (X.src φ) : QCoh (X.obj (X.src φ))),
      e.hom ≫ (B (X.src φ)).arrow =
        (QCoh.pullback (X.map φ)).map (B (X.dst φ)).arrow ≫ (F.iso φ).hom

/-- Compatibility means that each `α_φ` identifies `f_φ^* (B_{dst φ})` with `B_{src φ}` by an
isomorphism of subobjects. -/
theorem isCompatible_iff {X : RelDiagram.{u}} (F : Crystal X)
    (B : (i : X.index) → Subobject (F.obj i)) :
    IsCompatible F B ↔
      ∀ φ : X.arrow,
        ∃ e : (QCoh.pullback (X.map φ)).obj (B (X.dst φ) : QCoh (X.obj (X.dst φ))) ≅
            (B (X.src φ) : QCoh (X.obj (X.src φ))),
          CommSq e.hom ((QCoh.pullback (X.map φ)).map (B (X.dst φ)).arrow)
            (B (X.src φ)).arrow (F.iso φ).hom := sorry

/-- The compatible families of `κ`-generated quasi-coherent subsheaves of a crystal. -/
def kappaGeneratedSubobjects {X : RelDiagram.{u}} (κ : Cardinal.{u}) (F : Crystal X) :
    Set ((i : X.index) → Subobject (F.obj i)) :=
  { B | (∀ i, ((B i : QCoh (X.obj i)).obj).IsKappaGenerated κ) ∧ IsCompatible F B }

/-- Membership in `kappaGeneratedSubobjects` means componentwise `κ`-generation together with
compatibility of the family with the crystal isomorphisms. -/
@[simp] theorem mem_kappaGeneratedSubobjects {X : RelDiagram.{u}} (κ : Cardinal.{u})
    (F : Crystal X) (B : (i : X.index) → Subobject (F.obj i)) :
    B ∈ kappaGeneratedSubobjects κ F ↔
      (∀ i, ((B i : QCoh (X.obj i)).obj).IsKappaGenerated κ) ∧ IsCompatible F B := sorry

/-- Enlarging the cardinal bound preserves membership in the bounded compatible family. -/
theorem mem_kappaGeneratedSubobjects_of_le {X : RelDiagram.{u}} {κ κ' : Cardinal.{u}}
    {F : Crystal X} {B : (i : X.index) → Subobject (F.obj i)} (hκ : κ ≤ κ')
    (hB : B ∈ kappaGeneratedSubobjects κ F) :
    B ∈ kappaGeneratedSubobjects κ' F := sorry

/-- If every morphism of a pre-relation diagram of schemes is flat, there is a cardinal `κ`
depending only on the diagram such that every crystal in quasi-coherent modules is the
directed colimit of its `κ`-generated submodules. -/
theorem exists_cardinal_kappaGeneratedSubobjects_isDirectedColimit
    (X : RelDiagram.{u}) [∀ φ, Flat (X.map φ)] :
    ∃ κ : Cardinal.{u}, ∀ F : Crystal X,
      DirectedOn (· ≤ ·) (kappaGeneratedSubobjects κ F) ∧
        IsLUB (kappaGeneratedSubobjects κ F)
          (fun i ↦ (⊤ : Subobject (F.obj i))) := sorry

end AlgebraicGeometry.Scheme.RelDiagram.Crystal
