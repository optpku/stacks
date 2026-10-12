/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.DifferentialFormCohomology
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.BasicOpen
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LogarithmicForms
public import ReasLib.Algebra.Category.Ring.Sheaf.Units.Map
public import ReasLib.CategoryTheory.Sites.Cohomology.Zero
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Logarithmic Hodge generators on standard projective space

This file records the diagonal Hodge cohomology modules of standard projective space and the
Čech sections given by wedges of logarithmic differentials of consecutive coordinate-ratio
transition units.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open SheafOfModules.RingedSite.ExteriorPower
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- Diagonal Hodge cohomology of standard projective space in bidegree `(p, p)`. -/
abbrev hodgeCohomology (A : Type u) [CommRing A] (n p : ℕ) : ModuleCat A :=
  Scheme.Hom.cohomology (toSpec A n) (Λ[p] Ω[(toSpec A n).toShHom]) p

/-- The projective-space Hodge cohomology abbreviation expands to sheaf cohomology of
relative differential forms. -/
theorem hodgeCohomology_def (A : Type u) [CommRing A] (n p : ℕ) :
    hodgeCohomology A n p =
      Scheme.Hom.cohomology (toSpec A n) (Λ[p] Ω[(toSpec A n).toShHom]) p := rfl

/-- The support of the logarithmic Hodge cocycle: the whole space in degree zero, and the
intersection of the selected coordinate charts otherwise. -/
noncomputable def hodgeChernSupport (A : Type u) [CommRing A] (n p : ℕ)
    (I : Fin (p + 1) → Fin (n + 1)) : (scheme A n).Opens :=
  if p = 0 then ⊤
  else ⨅ k : Fin (p + 1), (coordinateBasicOpen (R := A) n (I k) : (scheme A n).Opens)

/-- The coordinate polynomial `T_i` is homogeneous of degree one. -/
theorem coordinate_isHomogeneous_one (A : Type u) [CommRing A] (n : ℕ)
    (i : Fin (n + 1)) :
    coordinate (R := A) n i ∈ grading A n 1 :=
  (MvPolynomial.mem_homogeneousSubmodule 1 (coordinate (R := A) n i)).2
    (MvPolynomial.isHomogeneous_X A i)

/-- The homogeneous localization away from the product of two coordinate polynomials. -/
abbrev coordinatePairAway (A : Type u) [CommRing A] (n : ℕ) (i j : Fin (n + 1)) :=
  HomogeneousLocalization.Away (grading A n)
    (coordinate (R := A) n i * coordinate (R := A) n j)

/-- The product `T_i T_j` is homogeneous of degree two. -/
theorem coordinate_mul_mem_grading_two (A : Type u) [CommRing A] (n : ℕ)
    (i j : Fin (n + 1)) :
    coordinate (R := A) n i * coordinate (R := A) n j ∈ grading A n 2 :=
  SetLike.mul_mem_graded
    (coordinate_isHomogeneous_one A n i)
    (coordinate_isHomogeneous_one A n j)

/-- The basic open of a product of two coordinates is the intersection of the two charts. -/
theorem coordinatePairBasicOpen_eq (A : Type u) [CommRing A] (n : ℕ)
    (i j : Fin (n + 1)) :
    basicOpen (R := A) n (coordinate (R := A) n i * coordinate (R := A) n j) =
      (coordinateBasicOpen (R := A) n i : (scheme A n).Opens) ⊓
        (coordinateBasicOpen (R := A) n j : (scheme A n).Opens) :=
  Proj.basicOpen_mul (grading A n)
    (coordinate (R := A) n i) (coordinate (R := A) n j)

/-- A multi-chart intersection is contained in each consecutive coordinate-pair overlap. -/
theorem hodgeChernSupport_le_coordinatePair (A : Type u) [CommRing A]
    (n p : ℕ) (hp : p ≠ 0) (I : Fin (p + 1) → Fin (n + 1)) (k : Fin p) :
    hodgeChernSupport A n p I ≤
      basicOpen (R := A) n
        (coordinate (R := A) n (I k.castSucc) * coordinate (R := A) n (I k.succ)) := by
  have hsup :
      hodgeChernSupport A n p I =
        ⨅ t : Fin (p + 1),
          (coordinateBasicOpen (R := A) n (I t) : (scheme A n).Opens) :=
    if_neg hp
  rw [hsup, coordinatePairBasicOpen_eq]
  exact le_inf (iInf_le _ k.castSucc) (iInf_le _ k.succ)

/-- The degree-zero fraction `T_j / T_i` in the homogeneous localization away from `T_i T_j`. -/
noncomputable def coordinatePairRatio (A : Type u) [CommRing A] (n : ℕ)
    (i j : Fin (n + 1)) : coordinatePairAway A n i j :=
  HomogeneousLocalization.Away.isLocalizationElem
    (coordinate_mul_mem_grading_two A n i j)
    (coordinate_isHomogeneous_one A n j)

/-- The inverse ratio `T_i / T_j` on `D₊(T_i T_j)`. -/
noncomputable def coordinatePairRatioInv (A : Type u) [CommRing A] (n : ℕ)
    (i j : Fin (n + 1)) : coordinatePairAway A n i j :=
  HomogeneousLocalization.Away.isLocalizationElem
    (coordinate_mul_mem_grading_two A n i j)
    (coordinate_isHomogeneous_one A n i)

/-- Consecutive coordinate ratios are inverse units on the pair overlap. -/
theorem coordinatePairRatio_mul_inv (A : Type u) [CommRing A] (n : ℕ)
    (i j : Fin (n + 1)) :
    coordinatePairRatio A n i j * coordinatePairRatioInv A n i j = 1 := by
  ext
  simp [coordinatePairRatio, coordinatePairRatioInv,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_one]
  rw [Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp
  ring

/-- Consecutive coordinate inverse ratios multiply to one in the opposite order. -/
theorem coordinatePairRatioInv_mul (A : Type u) [CommRing A] (n : ℕ)
    (i j : Fin (n + 1)) :
    coordinatePairRatioInv A n i j * coordinatePairRatio A n i j = 1 := by
  ext
  simp [coordinatePairRatio, coordinatePairRatioInv,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_one]
  rw [Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp
  ring

/-- The ratio `T_j / T_i` as a unit on `D₊(T_i T_j)`. -/
noncomputable def coordinatePairRatioUnit (A : Type u) [CommRing A] (n : ℕ)
    (i j : Fin (n + 1)) : (coordinatePairAway A n i j)ˣ where
  val := coordinatePairRatio A n i j
  inv := coordinatePairRatioInv A n i j
  val_inv := coordinatePairRatio_mul_inv A n i j
  inv_val := coordinatePairRatioInv_mul A n i j

/-- Canonical identification of the pair-overlap localization with sections on
`D₊(T_i) ∩ D₊(T_j)`. -/
noncomputable def coordinatePairSectionsIso (A : Type u) [CommRing A] (n : ℕ)
    (i j : Fin (n + 1)) :
    CommRingCat.of (coordinatePairAway A n i j) ≅
      Γ(scheme A n, basicOpen (R := A) n
        (coordinate (R := A) n i * coordinate (R := A) n j)) :=
  Proj.basicOpenIsoAway (grading A n)
    (coordinate (R := A) n i * coordinate (R := A) n j)
    (coordinate_mul_mem_grading_two A n i j) (by decide : 0 < 2)

/-- The unit `T_{I(k+1)} / T_{I k}` on the multi-chart intersection, obtained by restricting
the pair-overlap ratio. -/
noncomputable def hodgeChernTransitionUnit (A : Type u) [CommRing A]
    (n p : ℕ) (hp : p ≠ 0) (I : Fin (p + 1) → Fin (n + 1)) (k : Fin p) :
    ((scheme A n).sheaf.1.obj (op (hodgeChernSupport A n p I)))ˣ :=
  Units.map
    (((scheme A n).presheaf.map
        (homOfLE (hodgeChernSupport_le_coordinatePair A n p hp I k)).op).hom.toMonoidHom)
    (Units.map (coordinatePairSectionsIso A n (I k.castSucc) (I k.succ)).hom.hom.toMonoidHom
      (coordinatePairRatioUnit A n (I k.castSucc) (I k.succ)))

/-- The additive-units section determined by a consecutive coordinate-ratio transition. -/
noncomputable def hodgeChernTransition (A : Type u) [CommRing A]
    (n p : ℕ) (hp : p ≠ 0) (I : Fin (p + 1) → Fin (n + 1)) (k : Fin p) :
    (Sheaf.unitsAddSheaf (scheme A n).sheaf).1.obj (op (hodgeChernSupport A n p I)) :=
  Sheaf.unitsAddSheafSection (scheme A n).sheaf (hodgeChernTransitionUnit A n p hp I k)

/-- The logarithmic Čech cocycle whose component on the intersection of coordinate charts
`D₊(T_{I 0}) ∩ ⋯ ∩ D₊(T_{I p})` is `dlog(T_{I 1}/T_{I 0}) ∧ ⋯ ∧ dlog(T_{I p}/T_{I (p-1)})`.
In degree zero the component is the constant-one generator on the whole space. -/
noncomputable def hodgeChernPower (A : Type u) [CommRing A] (n p : ℕ)
    (I : Fin (p + 1) → Fin (n + 1)) :
    (Scheme.DeRham.additiveTerm (toSpec A n) p).1.obj
      (op (hodgeChernSupport A n p I)) :=
  if hp : p = 0 then
    (by
      subst hp
      exact Scheme.DeRham.logarithmicGenerator (toSpec A n) 0 ⊤ Fin.elim0)
  else
    Scheme.DeRham.logarithmicGenerator (toSpec A n) p (hodgeChernSupport A n p I)
      (hodgeChernTransition A n p hp I)

/-- The Hodge generator is the logarithmic Čech section of consecutive coordinate-ratio
units, or the constant-one generator in degree zero. -/
theorem hodgeChernPower_def (A : Type u) [CommRing A] (n p : ℕ)
    (I : Fin (p + 1) → Fin (n + 1)) :
    hodgeChernPower A n p I =
      if hp : p = 0 then
        (by
          subst hp
          exact Scheme.DeRham.logarithmicGenerator (toSpec A n) 0 ⊤ Fin.elim0)
      else
        Scheme.DeRham.logarithmicGenerator (toSpec A n) p (hodgeChernSupport A n p I)
          (hodgeChernTransition A n p hp I) := rfl

/-- Degree-zero Hodge cohomology of standard projective space, forgotten to additive groups,
is isomorphic to degree-zero cohomology of the degree-zero relative de Rham additive term
on the whole space. -/
theorem hodgeCohomology_zero_isIsomorphic_additiveTermH (A : Type u) [CommRing A] (n : ℕ) :
    IsIsomorphic
      ((forget₂ (ModuleCat A) AddCommGrpCat).obj (hodgeCohomology A n 0))
      ((Scheme.DeRham.additiveTerm (toSpec A n) 0).H' 0 (⊤ : (scheme A n).Opens)) := sorry

/-- For `1 ≤ n` and `p ≤ n`, the rank-one module `H^p(ℙⁿ_A, Ω^p)` admits a
`Fin 1` basis, unique up to `Aˣ`. In degree zero the named Čech section is the
constant-one logarithmic generator, and for positive degree the Čech representative is
the named logarithmic family `hodgeChernPower`. -/
theorem hodgeChernPower_basis (A : Type u) [CommRing A] (n : ℕ) (hn : 1 ≤ n)
    (p : ℕ) (hp : p ≤ n) :
    ∃ b : Module.Basis (Fin 1) A (hodgeCohomology A n p),
      Submodule.span A {(b (0 : Fin 1) : hodgeCohomology A n p)} = ⊤ ∧
        (∀ b' : Module.Basis (Fin 1) A (hodgeCohomology A n p),
          ∃ u : Aˣ,
            (b' (0 : Fin 1) : hodgeCohomology A n p) =
              u • (b (0 : Fin 1) : hodgeCohomology A n p)) ∧
        ((hp0 : p = 0) →
          hodgeChernPower A n 0 (fun _ => 0) =
            Scheme.DeRham.logarithmicGenerator (toSpec A n) 0 ⊤ Fin.elim0) ∧
        ((hpos : 0 < p) →
          ∀ I : Fin (p + 1) → Fin (n + 1),
            hodgeChernPower A n p I =
              Scheme.DeRham.logarithmicGenerator (toSpec A n) p
                (hodgeChernSupport A n p I)
                (hodgeChernTransition A n p (Nat.pos_iff_ne_zero.mp hpos) I)) := sorry

end AlgebraicGeometry.ProjectiveSpace
