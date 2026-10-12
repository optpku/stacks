/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Tensoring Universally Exact Short Complexes

Universal exactness is the owner-level condition ensuring that tensoring on the left by any
module preserves short exactness.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe u

namespace CategoryTheory.ShortComplex.UniversallyExact

variable {R : Type u} [CommRing R]

/-- Tensoring a universally exact short complex on the left preserves short exactness. -/
theorem tensorLeft_shortExact {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.UniversallyExact) (N : ModuleCat.{u} R) :
    (S.map (tensorLeft N)).ShortExact := by
  have hExact : Function.Exact S.f.hom S.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.shortExact.exact
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact (S.f.hom.lTensor N) (S.g.hom.lTensor N)
    exact lTensor_exact N hExact hS.shortExact.moduleCat_surjective_g
  · change Function.Injective (S.f.hom.lTensor N)
    rw [LinearMap.lTensor_inj_iff_rTensor_inj]
    exact hS.universallyInjective_f.rTensor_injective N
  · change Function.Surjective (S.g.hom.lTensor N)
    exact LinearMap.lTensor_surjective N hS.shortExact.moduleCat_surjective_g

end CategoryTheory.ShortComplex.UniversallyExact
