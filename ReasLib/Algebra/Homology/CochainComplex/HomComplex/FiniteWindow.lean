/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Module
public import ReasLib.CategoryTheory.Limits.Shapes.Products.Support

/-!
# Finite windows in module-valued Hom complexes

If the source complex is bounded above and the target is bounded below, each degree of their
Hom complex is supported on a finite interval of source degrees.  The public comparison uses the
canonical homogeneous family `degreeFamily R K L n p = Hom(K^p, L^(p+n))` and deletes its zero
factors through the generic product-support API.
-/

@[expose] public section

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.HomComplex

variable {R : Type w} [CommRing R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
variable {K L : CochainComplex C ℤ}

/-- A homogeneous Hom factor is zero when its source object is zero. -/
@[stacks 0A8H "zero Hom factor from a zero source"]
theorem degreeFamily_isZero_of_source {n p : ℤ} (hK : IsZero (K.X p)) :
    IsZero (degreeFamily R K L n p) := sorry

/-- A homogeneous Hom factor is zero when its target object is zero. -/
@[stacks 0A8H "zero Hom factor from a zero target"]
theorem degreeFamily_isZero_of_target {n p : ℤ} (hL : IsZero (L.X (p + n))) :
    IsZero (degreeFamily R K L n p) := sorry

/-- Under an upper bound on `K` and a lower bound on `L`, the homogeneous factors in degree `n`
vanish outside the interval `a - n ≤ p ≤ b`. -/
@[stacks 0A8H "finite support window for a module-valued Hom complex"]
theorem degreeFamily_isZero_outside_Icc {a b n p : ℤ}
    (hK : K.IsStrictlyLE b) (hL : L.IsStrictlyGE a)
    (hp : p ∉ Set.Icc (a - n) b) :
    IsZero (degreeFamily R K L n p) := sorry

/-- The degree-`n` term of a Hom complex from an upper-bounded source to a lower-bounded target
is the product over its finite source-degree window `a - n ≤ p ≤ b`. -/
@[stacks 0A8H "finite-window degree decomposition of a module-valued Hom complex"]
noncomputable def degreeIsoIcc {a b : ℤ}
    (hK : K.IsStrictlyLE b) (hL : L.IsStrictlyGE a) (n : ℤ) :
    (moduleComplex R K L).X n ≅
      ∏ᶜ fun p : Set.Icc (a - n) b ↦ degreeFamily R K L n p.1 :=
  (degreeIso R K L n).symm ≪≫
    Pi.isoSubtypeOfIsZero (degreeFamily R K L n)
      (fun p ↦ p ∈ Set.Icc (a - n) b)
      (fun p hp ↦ degreeFamily_isZero_outside_Icc
        (R := R) (K := K) (L := L) (n := n) (p := p) hK hL hp)

/-- The finite-window comparison followed by projection at `p` is the canonical enriched
projection at source degree `p`. -/
@[reassoc (attr := simp), stacks 0A8H "finite-window Hom projection"]
theorem degreeIsoIcc_hom_π {a b : ℤ}
    (hK : K.IsStrictlyLE b) (hL : L.IsStrictlyGE a)
    (n : ℤ) (p : Set.Icc (a - n) b) :
    (degreeIsoIcc hK hL n).hom ≫
        Pi.π (fun q : Set.Icc (a - n) b ↦ degreeFamily R K L n q.1) p =
      proj R K L n p.1 := sorry

/-- Extending a finite-window family back to the full Hom-complex degree and then projecting at
an index in the window recovers that coordinate. -/
@[reassoc (attr := simp), stacks 0A8H "finite-window Hom inverse projection"]
theorem degreeIsoIcc_inv_proj {a b : ℤ}
    (hK : K.IsStrictlyLE b) (hL : L.IsStrictlyGE a)
    (n : ℤ) (p : Set.Icc (a - n) b) :
    (degreeIsoIcc hK hL n).inv ≫ proj R K L n p.1 =
      Pi.π (fun q : Set.Icc (a - n) b ↦ degreeFamily R K L n q.1) p := sorry

end CochainComplex.HomComplex
