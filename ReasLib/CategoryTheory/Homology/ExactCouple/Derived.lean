/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.ExactCouple
public import ReasLib.CategoryTheory.Homology.ShortComplex.Cycles
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Abelian.Refinements

@[expose] public section

/-!
# Derived Exact Couples

This module separates the concrete data used to assemble a derived exact couple from the
proposition-valued laws which certify its relation to an input exact couple.  A
`Derived.Construction` supplies that data coherently at every iterate and hence produces an
associated spectral sequence without choosing data from an existential theorem.
-/

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace ExactCouple

namespace Derived

/-- The outer object of a derived exact couple: the image of the original outer endomorphism. -/
@[stacks 011S "derived outer object"]
abbrev outer (X : ExactCouple C) : C :=
  image X.α

/-- The endomorphism induced by `α` on its image. -/
@[stacks 011S "derived outer differential"]
abbrev alpha (X : ExactCouple C) : outer X ⟶ outer X :=
  image.map (Arrow.homMk X.α X.α rfl : Arrow.mk X.α ⟶ Arrow.mk X.α)

/-- Concrete data needed to construct the maps of one derived exact couple.

The proof fields are exactly the side conditions needed by the universal-property constructors;
the semantic comparison with the original exact couple belongs to `Laws`. -/
@[stacks 011S "derived exact-couple data"]
structure Data (X : ExactCouple C) where
  /-- A square-zero witness retained by the explicitly parameterized page complex. -/
  dSquared : X.d ≫ X.d = 0
  /-- The map from page cycles to the derived outer object. -/
  fCycles : ((X.pageOf dSquared).sc PUnit.unit).cycles ⟶ outer X
  /-- The cycle map vanishes on page boundaries. -/
  fCycles_zero : ((X.pageOf dSquared).sc PUnit.unit).toCycles ≫ fCycles = 0
  /-- The source-level representative of the derived map from the outer object to homology. -/
  gFromOuter : X.A ⟶ (X.pageOf dSquared).homology PUnit.unit
  /-- The source-level representative vanishes after the original map `f`. -/
  f_gFromOuter_zero : X.f ≫ gFromOuter = 0

namespace Data

variable {X : ExactCouple C}

/-- The page complex retained by a package of derived-couple data. -/
@[stacks 011S "derived page complex"]
noncomputable abbrev page (D : Data X) : HomologicalComplex C (ComplexShape.refl PUnit.{1}) :=
  X.pageOf D.dSquared

/-- The short complex at the unique degree of the retained page complex. -/
@[stacks 011S "derived page short complex"]
noncomputable abbrev shortComplex (D : Data X) : ShortComplex C :=
  D.page.sc PUnit.unit

/-- The homology object used as the middle object of the derived exact couple. -/
@[stacks 011S "derived page object"]
noncomputable abbrev homology (D : Data X) : C :=
  D.page.homology PUnit.unit

end Data

variable {X : ExactCouple C}

/-- The map from the retained page homology to the derived outer object. -/
@[stacks 011S "derived f map"]
noncomputable def f (D : Data X) : D.homology ⟶ outer X :=
  D.shortComplex.descHomology D.fCycles D.fCycles_zero

/-- The map from the derived outer object to the retained page homology. -/
@[stacks 011S "derived g map"]
noncomputable def g (D : Data X) : outer X ⟶ D.homology :=
  X.exact_f_α.isColimitImage.desc
    (CokernelCofork.ofπ D.gFromOuter D.f_gFromOuter_zero)

/-- Proposition-valued laws certifying that `Data` has the standard derived-exact-couple
meaning for the input exact couple. -/
@[stacks 011S "derived exact-couple laws"]
structure Laws (D : Data X) : Prop where
  /-- The cycle representative for the derived `f` agrees with the original `f` after inclusion
  into `A`. -/
  fCycles_comp_ι : D.fCycles ≫ image.ι X.α = D.shortComplex.iCycles ≫ X.f
  /-- The original map `g` is a cycle in the explicitly retained page complex. -/
  g_cycles : X.g ≫ D.shortComplex.g = 0
  /-- The selected representative `gFromOuter` is the homology class of the original `g`. -/
  gFromOuter_eq_lift :
    D.gFromOuter = D.shortComplex.liftToHomology X.g g_cycles
  /-- The derived maps satisfy the first zero-composite relation. -/
  f_comp_α : f D ≫ alpha X = 0
  /-- The derived maps satisfy the second zero-composite relation. -/
  g_comp_f : g D ≫ f D = 0
  /-- The derived maps satisfy the third zero-composite relation. -/
  α_comp_g : alpha X ≫ g D = 0
  /-- Exactness at the derived outer object after `f`. -/
  exact_f_α : (ShortComplex.mk (f D) (alpha X) f_comp_α).Exact
  /-- Exactness at the derived page object. -/
  exact_g_f : (ShortComplex.mk (g D) (f D) g_comp_f).Exact
  /-- Exactness at the derived outer object before `g`. -/
  exact_α_g : (ShortComplex.mk (alpha X) (g D) α_comp_g).Exact

/-- The derived `f` is represented on cycles by the original map `f`. -/
@[stacks 011S "derived f representative"]
theorem f_spec (D : Data X) (hD : Laws D) :
    D.shortComplex.homologyπ ≫ f D ≫ image.ι X.α =
      D.shortComplex.iCycles ≫ X.f := sorry

/-- The derived `g` descends from the selected source-level representative. -/
@[stacks 011S "derived g representative"]
theorem g_spec (D : Data X) (hD : Laws D) :
    factorThruImage X.α ≫ g D = D.gFromOuter := sorry

/-- The derived `g` is represented by the homology class of the original map `g`. -/
@[stacks 011S "derived g cycle representative"]
theorem g_spec_lift (D : Data X) (hD : Laws D) :
    factorThruImage X.α ≫ g D =
      D.shortComplex.liftToHomology X.g hD.g_cycles := sorry

/-- Assemble a derived exact couple from explicit data and its certified laws. -/
@[stacks 011S]
noncomputable def ofData {X : ExactCouple C} (D : Data X) (hD : Laws D) : ExactCouple C where
  A := outer X
  E := D.homology
  α := alpha X
  f := f D
  g := g D
  f_comp_α := hD.f_comp_α
  g_comp_f := hD.g_comp_f
  α_comp_g := hD.α_comp_g
  exact_f_α := hD.exact_f_α
  exact_g_f := hD.exact_g_f
  exact_α_g := hD.exact_α_g

/-- A coherent source of derived-couple data for every exact couple in the ambient category. -/
@[stacks 011S "iterable derived exact-couple construction"]
structure Construction (C : Type u) [Category.{v} C] [Abelian C] where
  /-- Concrete data for one derivation step. -/
  data : (X : ExactCouple C) → Data X
  /-- Proposition-valued certification of the data for one derivation step. -/
  laws : (X : ExactCouple C) → Laws (data X)

namespace Construction

/-- Derive an exact couple using the data selected by a coherent construction. -/
@[stacks 011S "derived exact couple"]
noncomputable def derived (K : Construction C) (X : ExactCouple C) : ExactCouple C :=
  ofData (K.data X) (K.laws X)

/-- Iterate a coherent derived-exact-couple construction. -/
@[stacks 011S "iterated derived couple"]
noncomputable def iterate (K : Construction C) (X : ExactCouple C) : ℕ → ExactCouple C
  | 0 => X
  | n + 1 => K.derived (K.iterate X n)

namespace Iteration

/-- The zeroth iteration is the input exact couple. -/
@[simp]
theorem zero (K : Construction C) (X : ExactCouple C) : K.iterate X 0 = X := sorry

/-- The middle object of the zeroth iteration is the input page object. -/
@[simp]
theorem zero_E (K : Construction C) (X : ExactCouple C) : (K.iterate X 0).E = X.E := sorry

/-- The page differential of the zeroth iteration is the input page differential. -/
@[simp]
theorem zero_d (K : Construction C) (X : ExactCouple C) :
    (K.iterate X 0).d = X.d := sorry

/-- The successor iteration derives the preceding exact couple. -/
@[simp]
theorem succ (K : Construction C) (X : ExactCouple C) (n : ℕ) :
    K.iterate X (n + 1) = K.derived (K.iterate X n) := sorry

end Iteration

/-- The spectral sequence associated to a coherently iterable derived exact-couple construction. -/
@[stacks 011S "associated spectral sequence"]
noncomputable def associatedSpectralSequence (K : Construction C) (X : ExactCouple C) :
    SpectralSequence C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1 where
  page r hr := match r with
    | Int.ofNat 0 => nomatch hr
    | Int.ofNat (n + 1) => (K.data (K.iterate X n)).page
    | Int.negSucc _ => nomatch hr
  iso r _ _ hrr' hr := match r with
    | Int.ofNat 0 => nomatch hr
    | Int.negSucc _ => nomatch hr
    | Int.ofNat (_ + 1) => match hrr' with
      | rfl => Iso.refl _

end Construction

namespace Page

/-- The page at index `r + 1` is the explicitly retained page complex of the `r`-fold iterate. -/
@[stacks 011S "associated page complex"]
theorem complex (K : Construction C) (X : ExactCouple C) (r : ℕ) :
    (K.associatedSpectralSequence X).page (Nat.succ r : ℤ) =
      (K.data (K.iterate X r)).page := sorry

/-- The page object at index `r + 1` is the middle object of the `r`-fold iterate. -/
@[stacks 011S "associated page object"]
theorem obj (K : Construction C) (X : ExactCouple C) (r : ℕ) :
    ((K.associatedSpectralSequence X).page (Nat.succ r : ℤ)).X PUnit.unit =
      (K.iterate X r).E := sorry

/-- The page differential at index `r + 1` is the differential of the `r`-fold iterate. -/
@[stacks 011S "associated page differential"]
theorem differential (K : Construction C) (X : ExactCouple C) (r : ℕ) :
    ((K.associatedSpectralSequence X).page (Nat.succ r : ℤ)).d PUnit.unit PUnit.unit =
      (K.iterate X r).d := sorry

end Page

end Derived

end ExactCouple

end CategoryTheory
