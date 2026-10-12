/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Transporting a Double Complex Across Column Isomorphisms

This leaf transports the horizontal differential of a double complex through a family of
isomorphisms of its columns.  It is independent of resolutions, boundedness, totalization, and
any particular choice of complex shape.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u w₁ w₂

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {I₁ : Type w₁} {I₂ : Type w₂}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

namespace Column.Transport

/-- 015J: the horizontal differential transported from `K` to a family of isomorphic columns. -/
@[stacks 015J "transported horizontal differential"]
noncomputable def d
    (K : HomologicalComplex₂ C c₁ c₂)
    {L : I₁ → HomologicalComplex C c₂}
    (e : ∀ p, L p ≅ K.X p) (p r : I₁) :
    L p ⟶ L r :=
  (e p).hom ≫ K.d p r ≫ (e r).inv

/-- The component of the transported horizontal differential is obtained by conjugating the
corresponding component of `K.d`. -/
@[simp]
theorem d_f
    (K : HomologicalComplex₂ C c₁ c₂)
    {L : I₁ → HomologicalComplex C c₂}
    (e : ∀ p, L p ≅ K.X p) (p r : I₁) (q : I₂) :
    (d K e p r).f q =
      (e p).hom.f q ≫ (K.d p r).f q ≫ (e r).inv.f q := sorry

/-- 015J: the double complex obtained by replacing each column of `K` by an isomorphic
column. -/
@[stacks 015J "double complex transported across column isomorphisms"]
noncomputable def bicomplex
    (K : HomologicalComplex₂ C c₁ c₂)
    {L : I₁ → HomologicalComplex C c₂}
    (e : ∀ p, L p ≅ K.X p) :
    HomologicalComplex₂ C c₁ c₂ where
  X := L
  d p r := d K e p r
  shape := sorry
  d_comp_d' := sorry

/-- The column in horizontal degree `p` of the transported double complex is the chosen
replacement column. -/
@[simp]
theorem bicomplex_X
    (K : HomologicalComplex₂ C c₁ c₂)
    {L : I₁ → HomologicalComplex C c₂}
    (e : ∀ p, L p ≅ K.X p) (p : I₁) :
    (bicomplex K e).X p = L p := sorry

/-- The horizontal differential of the transported double complex is `Column.Transport.d`. -/
@[simp]
theorem bicomplex_d
    (K : HomologicalComplex₂ C c₁ c₂)
    {L : I₁ → HomologicalComplex C c₂}
    (e : ∀ p, L p ≅ K.X p) (p r : I₁) :
    (bicomplex K e).d p r = d K e p r := sorry

/-- The forward column isomorphisms intertwine the transported and original horizontal
differentials. -/
@[reassoc]
theorem iso_hom_d
    (K : HomologicalComplex₂ C c₁ c₂)
    {L : I₁ → HomologicalComplex C c₂}
    (e : ∀ p, L p ≅ K.X p) (p r : I₁) :
    (e p).hom ≫ K.d p r = d K e p r ≫ (e r).hom := sorry

/-- The inverse column isomorphisms intertwine the original and transported horizontal
differentials. -/
@[reassoc]
theorem iso_inv_d
    (K : HomologicalComplex₂ C c₁ c₂)
    {L : I₁ → HomologicalComplex C c₂}
    (e : ∀ p, L p ≅ K.X p) (p r : I₁) :
    (e p).inv ≫ d K e p r = K.d p r ≫ (e r).inv := sorry

/-- 015J: the canonical double-complex isomorphism from transported columns back to `K`. -/
@[stacks 015J "column-transport double-complex isomorphism"]
noncomputable def iso
    (K : HomologicalComplex₂ C c₁ c₂)
    {L : I₁ → HomologicalComplex C c₂}
    (e : ∀ p, L p ≅ K.X p) :
    bicomplex K e ≅ K :=
  HomologicalComplex.Hom.isoOfComponents e (fun p r _ => iso_hom_d K e p r)

/-- Evaluating the column-transport isomorphism recovers the specified column isomorphism. -/
@[simp]
theorem iso_app
    (K : HomologicalComplex₂ C c₁ c₂)
    {L : I₁ → HomologicalComplex C c₂}
    (e : ∀ p, L p ≅ K.X p) (p : I₁) :
    HomologicalComplex.Hom.isoApp (iso K e) p = e p := sorry

/-- The forward component of the column-transport isomorphism is the specified column map. -/
@[simp]
theorem iso_hom_f
    (K : HomologicalComplex₂ C c₁ c₂)
    {L : I₁ → HomologicalComplex C c₂}
    (e : ∀ p, L p ≅ K.X p) (p : I₁) :
    (iso K e).hom.f p = (e p).hom := sorry

/-- The inverse component of the column-transport isomorphism is the inverse specified column
map. -/
@[simp]
theorem iso_inv_f
    (K : HomologicalComplex₂ C c₁ c₂)
    {L : I₁ → HomologicalComplex C c₂}
    (e : ∀ p, L p ≅ K.X p) (p : I₁) :
    (iso K e).inv.f p = (e p).inv := sorry

end Column.Transport

end HomologicalComplex₂
