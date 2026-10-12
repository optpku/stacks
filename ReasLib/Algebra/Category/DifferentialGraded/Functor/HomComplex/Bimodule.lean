/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor.HomComplex
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Diagonal
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Endomorphism

/-!
# Cross-Hom Differential Graded Bimodules

The enriched Hom complex from `K` to `L` carries commuting actions by the endomorphism
DG algebras of `L` and `K`, through postcomposition and precomposition respectively.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedCategory.HomComplex

variable {R : Type u} [CommRing R]
variable {C : Type v} [D : DifferentialGradedCategory.{u, v, w} R C]

/-- Graded precomposition of an element of `homComplex K L` by an endomorphism of `K`. -/
def rightMulValue (K L : C) (p i : ℤ) (f : K ⟶[p] L) (a : K ⟶[i] K) :
    K ⟶[p + i] L :=
  castHom (add_comm i p) (D.comp f a)

/-- Graded precomposition as a bilinear right action of `endomorphismDGA K`. -/
def rightMul (K L : C) (p i : ℤ) :
    homComponent K L p →ₗ[R] homComponent K K i →ₗ[R] homComponent K L (p + i) where
  toFun f :=
    { toFun := rightMulValue K L p i f
      map_add' := sorry
      map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

/-- The enriched Hom complex `homComplex K L` as a right DG module over
`endomorphismDGA K`, with action by graded precomposition. -/
def rightModule (K L : C) :
    DifferentialGradedModule.{u, w} (endomorphismDGA K) where
  X := homComponent K L
  d := homDifferential K L
  smul := rightMul K L
  d_sq := sorry
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- Forgetting the precomposition action recovers the enriched Hom complex. -/
theorem rightModule_toCochainComplex (K L : C) :
    (rightModule K L).toCochainComplex = homComplex K L := sorry

/-- The right action on `rightModule K L` is graded precomposition. -/
theorem rightModule_smul (K L : C) (p i : ℤ)
    (f : (rightModule K L).X p) (a : (endomorphismDGA K).X i) :
    (rightModule K L).smul p i f a = rightMulValue K L p i f a := sorry

/-- Graded postcomposition of an element of `homComplex K L` by an endomorphism of `L`. -/
def leftMulValue (K L : C) (i p : ℤ) (a : L ⟶[i] L) (f : K ⟶[p] L) :
    K ⟶[i + p] L :=
  castHom (add_comm p i) (D.comp a f)

/-- Graded postcomposition as a bilinear left action of `endomorphismDGA L`. -/
def leftMul (K L : C) (i p : ℤ) :
    homComponent L L i →ₗ[R] homComponent K L p →ₗ[R] homComponent K L (i + p) where
  toFun a :=
    { toFun := leftMulValue K L i p a
      map_add' := sorry
      map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

/-- The compatible left action of `endomorphismDGA L` on `rightModule K L`, given by
graded postcomposition. -/
def leftAction (K L : C) :
    DifferentialGradedBimodule.LeftAction (endomorphismDGA L) (rightModule K L) where
  leftMul := leftMul K L
  left_assoc := sorry
  one_left := sorry
  comm_right := sorry
  d_leftMul := sorry

/-- The cross-Hom complex from `K` to `L`, as a DG bimodule with left
`endomorphismDGA L`-action and right `endomorphismDGA K`-action. -/
def bimodule (K L : C) :
    DifferentialGradedBimodule.{u, w, w, w} (endomorphismDGA L) (endomorphismDGA K) :=
  (leftAction K L).toBimodule

/-- Degree `n` of the cross-Hom bimodule is the degree-`n` homogeneous morphism module
from `K` to `L`. -/
theorem bimodule_X (K L : C) (n : ℤ) :
    (bimodule K L).X n = homComponent K L n := sorry

/-- The left action on the cross-Hom bimodule is graded postcomposition. -/
theorem bimodule_leftMul (K L : C) (i p : ℤ)
    (a : (endomorphismDGA L).X i) (f : (bimodule K L).X p) :
    (bimodule K L).leftMul i p a f = leftMulValue K L i p a f := sorry

/-- The right action on the cross-Hom bimodule is graded precomposition. -/
theorem bimodule_rightMul (K L : C) (p i : ℤ)
    (f : (bimodule K L).X p) (a : (endomorphismDGA K).X i) :
    (bimodule K L).rightMul p i f a = rightMulValue K L p i f a := sorry

/-- The self-Hom bimodule agrees with the diagonal bimodule of the endomorphism DGA. -/
theorem bimodule_self (K : C) :
    bimodule K K = DifferentialGradedBimodule.diagonal (endomorphismDGA K) := sorry

end DifferentialGradedCategory.HomComplex
