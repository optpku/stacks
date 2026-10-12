/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap95.Example_95_17_1_FixedLocus
public import stacks_project.Chap95.Remark_95_15_5_Quotient

/-!
# Disjoint union of quotient stacks of fixed loci

The family `[[X^g/G]]` and the disjoint union of their total categories, as a category
over `(Sch/S)_fppf`. This coproduct is not itself a stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.QuotientStack.AbstractGroup
open AlgebraicGeometry.QuotientStack.FixedLocus

noncomputable section

universe u

namespace AlgebraicGeometry.QuotientStack.InertiaCoprod

variable {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}

/-- The quotient stack `[[X^g/G]]` of the residual action on the fixed locus. -/
def fixedQuotient (ρ : G →* Aut X) (g : G) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  stack (ofOverAut.comp (residual ρ g))

/-- The projection of `fixedQuotient ρ g` is the forgetful functor of the residual action. -/
theorem fixedQuotient_p (ρ : G →* Aut X) (g : G) :
    (fixedQuotient ρ g).p = forget (ofOverAut.comp (residual ρ g)) :=
  sorry

/-- An object of the disjoint union of the categories `[[X^g/G]]`. -/
structure CoprodObj (ρ : G →* Aut X) where
  /-- The index `g ∈ G` of the summand `[[X^g/G]]`. -/
  idx : G
  /-- An object of `[[X^g/G]]`. -/
  obj : Obj (ofOverAut.comp (residual ρ idx))

/-- Include an object of `[[X^g/G]]` as a summand of the disjoint union. -/
def ofSummand (ρ : G →* Aut X) (g : G)
    (ξ : Obj (ofOverAut.comp (residual ρ g))) : CoprodObj ρ where
  idx := g
  obj := ξ

/-- The constructor of `CoprodObj` stores the supplied index and object. -/
theorem ofSummand_spec (ρ : G →* Aut X) (g : G)
    (ξ : Obj (ofOverAut.comp (residual ρ g))) :
    (ofSummand ρ g ξ).idx = g ∧ (ofSummand ρ g ξ).obj = ξ :=
  sorry

/-- A morphism in the disjoint union exists only between objects with the same index, and is
then a morphism of the corresponding `[[X^g/G]]`. -/
inductive CoprodHom {ρ : G →* Aut X} : CoprodObj ρ → CoprodObj ρ → Type (u + 1) where
  | mk : ∀ {g : G} {ξ ξ' : Obj (ofOverAut.comp (residual ρ g))},
      (ξ ⟶ ξ') → CoprodHom ⟨g, ξ⟩ ⟨g, ξ'⟩

/-- The identity morphism of a summand object. -/
def idHom {ρ : G →* Aut X} (ξ : CoprodObj ρ) : CoprodHom ξ ξ :=
  match ξ with
  | ⟨_, obj⟩ => CoprodHom.mk (𝟙 obj)

/-- Composition of morphisms in the disjoint union. -/
def compHom {ρ : G →* Aut X} {ξ ξ' ξ'' : CoprodObj ρ} :
    CoprodHom ξ ξ' → CoprodHom ξ' ξ'' → CoprodHom ξ ξ'' :=
  fun α β ↦
    match α, β with
    | CoprodHom.mk f, CoprodHom.mk g => CoprodHom.mk (f ≫ g)

/-- Left identity law for the disjoint union. -/
theorem idHom_comp {ρ : G →* Aut X} {ξ ξ' : CoprodObj ρ} (α : CoprodHom ξ ξ') :
    compHom (idHom ξ) α = α :=
  sorry

/-- Right identity law for the disjoint union. -/
theorem compHom_id {ρ : G →* Aut X} {ξ ξ' : CoprodObj ρ} (α : CoprodHom ξ ξ') :
    compHom α (idHom ξ') = α :=
  sorry

/-- Associativity of composition in the disjoint union. -/
theorem assocHom {ρ : G →* Aut X} {ξ₁ ξ₂ ξ₃ ξ₄ : CoprodObj ρ}
    (α : CoprodHom ξ₁ ξ₂) (β : CoprodHom ξ₂ ξ₃) (γ : CoprodHom ξ₃ ξ₄) :
    compHom (compHom α β) γ = compHom α (compHom β γ) :=
  sorry

/-- The disjoint union of the categories `[[X^g/G]]`. -/
instance instCategory (ρ : G →* Aut X) : Category (CoprodObj ρ) where
  Hom := CoprodHom
  id := idHom
  comp := compHom
  id_comp := idHom_comp
  comp_id := compHom_id
  assoc := assocHom

/-- The underlying scheme map of a coproduct morphism. -/
def homScheme {ρ : G →* Aut X} {ξ ξ' : CoprodObj ρ} (α : CoprodHom ξ ξ') :
    ξ.obj.U ⟶ ξ'.obj.U :=
  match α with
  | CoprodHom.mk f => f.f

/-- The projection of the disjoint union to `(Sch/S)_fppf`. -/
def p (ρ : G →* Aut X) : CoprodObj ρ ⥤ Over S where
  obj ξ := ξ.obj.U
  map α := homScheme α
  map_id := sorry
  map_comp := sorry

/-- The projection sends a pair `(g, (U, P, φ))` to `U`. -/
theorem p_obj {ρ : G →* Aut X} (ξ : CoprodObj ρ) : (p ρ).obj ξ = ξ.obj.U :=
  sorry

/-- The projection sends a coproduct morphism to its underlying scheme map. -/
theorem p_map {ρ : G →* Aut X} {ξ ξ' : CoprodObj ρ} (α : ξ ⟶ ξ') :
    (p ρ).map α = homScheme α :=
  sorry

/-- The disjoint union of groupoid-fibered categories over `(Sch/S)_fppf` is fibered in
groupoids. -/
instance instIsFiberedInGroupoids (ρ : G →* Aut X) :
    Functor.IsFibered.InGroupoids (p ρ) :=
  sorry

end AlgebraicGeometry.QuotientStack.InertiaCoprod
