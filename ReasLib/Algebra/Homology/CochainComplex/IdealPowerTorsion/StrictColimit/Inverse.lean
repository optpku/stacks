/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.IdealPowerTorsion.StrictColimit.ReverseData

/-!
Canonical-source DATA assembly for the explicit inverse of the actual strict colimit evaluation.

The carrier is the existing categorical colimit of `strictDiagram I J` in the category
of unbounded integer-indexed cochain complexes.  The inverse is assembled in the
following order:

* `colimitRepresentative` is the existing chosen-exponent stage representative;
* `reverseTerm` packages that function as an actual `A`-linear map at one degree;
* `reverseCochainMap` packages those degree maps with the cochain differential law;
* `strictColimitInverseIso` supplies that explicit map as `Iso.inv` and keeps the
  existing `colimitEvaluation` as `Iso.hom`.

The map laws and the two inverse laws are true propositions.  They remain
individual Prop debt under the requested scope.  The left composite is to be
proved categorically with `colimit.hom_ext` after every actual stage injection,
then `colimit.ι_desc`, common-stage independence, and `colimit.w`; this does
not assume pointwise evaluation preserves colimits or element-surjectivity.
No `Nonempty` witness or desired inverse is selected.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex

namespace CochainComplex.IdealPowerTorsion.StrictColimitInverseAssembly

open CochainComplex.IdealPowerTorsion
open CochainComplex.IdealPowerTorsion.StrictColimitReverseData

variable {A : Type u} [CommRing A]

section Colimit

variable (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ)
variable [HasColimit (strictDiagram I J)]

/-- Additivity of the chosen stage representative, as a true Prop law. -/
theorem colimitRepresentative_add (q : ℤ)
    (x y : (gamma I J).X q) :
    colimitRepresentative I J q (x + y) =
      colimitRepresentative I J q x + colimitRepresentative I J q y := by
  sorry

/-- Scalar compatibility of the chosen stage representative, as a true Prop law. -/
theorem colimitRepresentative_smul (q : ℤ) (a : A)
    (x : (gamma I J).X q) :
    colimitRepresentative I J q (a • x) =
      a • colimitRepresentative I J q x := by
  sorry

/-- Differential compatibility of the chosen stage representative, as a true Prop law. -/
theorem colimitRepresentative_d (q : ℤ) (x : (gamma I J).X q) :
    ((colimit (strictDiagram I J)).d q (q + 1)).hom
        (colimitRepresentative I J q x) =
      colimitRepresentative I J (q + 1)
        (((gamma I J).d q (q + 1)).hom x) := by
  sorry

/--
The actual degree-`q` linear component of the inverse.  Its computational function
is exactly `colimitRepresentative`; only its additive and scalar laws are Prop data.
-/
noncomputable def reverseTerm (q : ℤ) :
    (gamma I J).X q →ₗ[A] (colimit (strictDiagram I J)).X q where
  toFun := colimitRepresentative I J q
  map_add' x y := colimitRepresentative_add I J q x y
  map_smul' a x := colimitRepresentative_smul I J q a x

@[simp]
theorem reverseTerm_apply (q : ℤ) (x : (gamma I J).X q) :
    reverseTerm I J q x = colimitRepresentative I J q x := rfl

/--
The actual cochain-map differential law for the degreewise linear components.
The proof uses the same common-stage argument as
`colimitRepresentative_d`: transport both representatives to a common stage,
use `singleRead_d`, and close with `colimit.w`.
-/
theorem reverseTerm_d (q : ℤ) (x : (gamma I J).X q) :
    ((colimit (strictDiagram I J)).d q (q + 1)).hom
        (reverseTerm I J q x) =
      reverseTerm I J (q + 1)
        (((gamma I J).d q (q + 1)).hom x) := by
  simpa only [reverseTerm_apply] using colimitRepresentative_d I J q x

/-- The reverse degreewise maps assembled as one actual cochain morphism. -/
noncomputable def reverseCochainMap :
    gamma I J ⟶ colimit (strictDiagram I J) where
  f q := ModuleCat.ofHom (reverseTerm I J q)
  comm' := by
    intro p q hpq
    obtain rfl : p + 1 = q := hpq
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change
      ((colimit (strictDiagram I J)).d p (p + 1)).hom
          (reverseTerm I J p x) =
        reverseTerm I J (p + 1)
          (((gamma I J).d p (p + 1)).hom x)
    exact reverseTerm_d I J p x

@[simp]
theorem reverseCochainMap_f (q : ℤ) :
    (reverseCochainMap I J).f q = ModuleCat.ofHom (reverseTerm I J q) := rfl

/--
The existing evaluation followed by the explicit reverse map is the identity on
the actual colimit.  This is a Prop obligation: compare the two maps with
`colimit.hom_ext` after each actual stage injection, use `colimit.ι_desc`, the
common-stage independence law, and `colimit.w`; no pointwise evaluation-preserves-
colimits or element-surjectivity theorem is assumed.
-/
theorem colimitEvaluation_comp_reverseCochainMap :
    colimitEvaluation I J ≫ reverseCochainMap I J =
      𝟙 (colimit (strictDiagram I J)) := by
  sorry

/--
The explicit reverse map followed by the existing evaluation is the identity on
`gamma`.  On each degree this is `stageLift_evaluates`, followed by
`colimitEvaluation_ι`; no inverse is selected by existence.
-/
theorem reverseCochainMap_comp_colimitEvaluation :
    reverseCochainMap I J ≫ colimitEvaluation I J =
      𝟙 (gamma I J) := by
  sorry

/--
An explicit isomorphism whose hom is the already specified colimit evaluation and
whose inverse is the assembled reverse cochain map.
-/
noncomputable def strictColimitInverseIso :
    colimit (strictDiagram I J) ≅ gamma I J where
  hom := colimitEvaluation I J
  inv := reverseCochainMap I J
  hom_inv_id := colimitEvaluation_comp_reverseCochainMap I J
  inv_hom_id := reverseCochainMap_comp_colimitEvaluation I J

@[simp]
theorem strictColimitInverseIso_hom :
    (strictColimitInverseIso I J).hom = colimitEvaluation I J := rfl

@[simp]
theorem strictColimitInverseIso_inv :
    (strictColimitInverseIso I J).inv = reverseCochainMap I J := rfl

end Colimit

end CochainComplex.IdealPowerTorsion.StrictColimitInverseAssembly

end
