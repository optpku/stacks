/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.CommSq

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Over.Polynomial

variable (R : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec R)]

/-- An object consists of an open subscheme of `X`, an actual scheme over `Spec R`,
an arrow from the open subscheme to that scheme, and a presentation of the scheme
as a polynomial affine space over `Spec R`. -/
structure Object where
  /-- The open subscheme of `X`. -/
  U : X.Opens
  /-- The actual scheme at the affine-space vertex. -/
  A : Scheme.{u}
  /-- The structure morphism of the vertex to `Spec R`. -/
  toBase : A ⟶ Spec R
  /-- The morphism from the open subscheme to the affine-space vertex. -/
  toAffine : U.toScheme ⟶ A
  /-- The vertex is isomorphic over `Spec R` to a standard polynomial affine space. -/
  isAffineSpace :
    ∃ ι : Type u,
      Nonempty (CategoryTheory.Over.mk toBase ≅
        CategoryTheory.Over.mk (𝔸(ι; Spec R) ↘ Spec R))
  /-- The square formed by the two displayed morphisms commutes. -/
  w : toAffine ≫ toBase = U.ι ≫ X ↘ Spec R

namespace Object

variable {R X}

/-- The object determined by an open subscheme and a family of global sections on it. -/
def ofVector (U : X.Opens) (ι : Type u) (v : ι → Γ(U.toScheme, ⊤)) : Object R X where
  U := U
  A := 𝔸(ι; Spec R)
  toBase := 𝔸(ι; Spec R) ↘ Spec R
  toAffine := AffineSpace.homOfVector (U.toScheme ↘ Spec R) v
  isAffineSpace := ⟨ι, ⟨CategoryTheory.Iso.refl _⟩⟩
  w := AffineSpace.homOfVector_over (U.toScheme ↘ Spec R) v

/-- The open subscheme of the object constructed from a family of global sections. -/
theorem ofVector_U (U : X.Opens) (ι : Type u) (v : ι → Γ(U.toScheme, ⊤)) :
    (ofVector U ι v : Object R X).U = U := sorry

/-- The affine-space vertex of the object constructed from a family of global sections. -/
theorem ofVector_A (U : X.Opens) (ι : Type u) (v : ι → Γ(U.toScheme, ⊤)) :
    (ofVector U ι v : Object R X).A = 𝔸(ι; Spec R) := sorry

/-- The morphism from the open subscheme in the object constructed from a family of
global sections to its affine-space vertex. -/
theorem ofVector_toAffine (U : X.Opens) (ι : Type u) (v : ι → Γ(U.toScheme, ⊤)) :
    (ofVector U ι v).toAffine = AffineSpace.homOfVector (U.toScheme ↘ Spec R) v := sorry

/-- The commuting square associated to an object. -/
def commSq (obj : Object R X) :
    CommSq obj.toAffine obj.U.ι obj.toBase (X ↘ Spec R) :=
  ⟨obj.w⟩

/-- The defining properties of an object: its square commutes and its vertex has a
polynomial-spectrum presentation over `Spec R`. -/
theorem spec (obj : Object R X) :
    CommSq obj.toAffine obj.U.ι obj.toBase (X ↘ Spec R) ∧
      ∃ ι : Type u,
        Nonempty (CategoryTheory.Over.mk obj.toBase ≅
          CategoryTheory.Over.mk
            (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial ι R)))) := sorry

end Object

end AlgebraicGeometry.Scheme.Over.Polynomial
