/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommLocalHomComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Products

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace LocalHomDiagonalProduct
variable {A R : Type (u + 1)} [CommRing A] [Ring R]
variable (h : A →+* R) (hc : ∀ (a : A) (r : R), h a * r = r * h a)
variable (Y : Scheme.{u})
variable [Y.smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable (L : ChainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ)
variable (J : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℕ)

def diagram (n : ℕ) := Discrete.functor (NoncommLocalHomComplex.factor h hc Y L J n)

/-- The product cone has precisely Kuhn's actual coordinate projections. -/
def cone (n : ℕ) : Cone (diagram h hc Y L J n) where
  pt := NoncommLocalHomComplex.degree h hc Y L J n
  π := Discrete.natTrans (fun i ↦ NoncommLocalHomComplex.projection h hc Y L J n i.as)

/-- Its universal lift is the already specified pointwise finite-product lift;
no product object or comparison function is postulated. -/
def isLimit (n : ℕ) : IsLimit (cone h hc Y L J n) where
  lift s := NoncommLocalHomComplex.lift h hc Y L J n (fun i ↦ s.π.app (Discrete.mk i))
  fac := by sorry
  uniq := by sorry

end LocalHomDiagonalProduct
