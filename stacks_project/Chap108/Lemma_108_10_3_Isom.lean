module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import stacks_project.Chap99.Lemma_99_12_1_Mor

/-!
# The Isom subfunctor of relative morphisms

The subfunctor `Isom_B(Y, X) ⊂ Mor_B(Y, X)` on schemes over `B`, whose
sections are the isomorphisms `Y_T ⟶ X_T` over `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.Quot (SchemesOver)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Y B X : AlgebraicSpace S}

/-- Restriction of an isomorphism `Y_T ⟶ X_T` over `T` along a morphism of
schemes over `B` remains an isomorphism. -/
theorem restrict_isIso (y : Y ⟶ B) (x : X ⟶ B) {σ τ : SchemesOver B}
    (h : τ ⟶ σ) {b : BaseChangeMorphism y x σ.hom} (hb : IsIso b) :
    IsIso (restrict y x h b) :=
  sorry

/-- The subfunctor of `Mor_B(Y, X)` whose value on a scheme `T` over `B` is the
set of isomorphisms `Y_T ⟶ X_T` over `T`. -/
def isomSubfunctor (y : Y ⟶ B) (x : X ⟶ B) : Subfunctor (mor y x) where
  obj _ := {b | IsIso b}
  map h _ hb := restrict_isIso y x h.unop hb

/-- The Type-valued functor `Isom_B(Y, X)` associated to the isomorphism
subfunctor of `Mor_B(Y, X)`. -/
def isom (y : Y ⟶ B) (x : X ⟶ B) : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1) :=
  (isomSubfunctor y x).toFunctor

/-- Membership in the Isom subfunctor is invertibility of the corresponding
relative morphism over the test scheme. -/
theorem mem_isomSubfunctor (y : Y ⟶ B) (x : X ⟶ B) {σ : SchemesOver B}
    (b : (mor y x).obj (op σ)) :
    b ∈ (isomSubfunctor y x).obj (op σ) ↔ IsIso b :=
  sorry

/-- Package an already invertible relative morphism as a section of
`Isom_B(Y, X)`. -/
def isom_mk (y : Y ⟶ B) (x : X ⟶ B) {σ : SchemesOver B}
    (b : BaseChangeMorphism y x σ.hom) [IsIso b] :
    (isom y x).obj (op σ) :=
  ⟨b, ‹IsIso b›⟩

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
