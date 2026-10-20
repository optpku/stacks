/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.UniversalFiniteFree.Classification
public import ReasLib.AlgebraicGeometry.Scheme.UniversalFiniteFree
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec

/-!
# Points of the universal finite free algebra scheme

Morphisms to the universal coefficient spectrum classify distinguished algebra
structures over global sections.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace UniversalFiniteFreeAlgebra

/-- Morphisms to the universal coefficient spectrum correspond to ring maps
from its coefficient ring to global sections. -/
def schemeHomCoeff (T : Scheme) (d : ℕ+) :
    (T ⟶ baseScheme d) ≃ (CoefficientRing d →+* Γ(T, ⊤)) :=
  (Scheme.homToSpecGlobalSectionsEquiv T (CommRingCat.of (CoefficientRing d))).trans
    { toFun := CommRingCat.Hom.hom
      invFun := CommRingCat.ofHom
      left_inv := CommRingCat.ofHom_hom
      right_inv := CommRingCat.hom_ofHom }

/-- Ring maps from the universal coefficient ring to global sections classify
distinguished algebra structures over those global sections. -/
def schemeHomFreeDimAlgebra (T : Scheme.{u}) (d : ℕ+) :
    (CoefficientRing d →+* Γ(T, ⊤)) ≃ FreeDimAlgebra Γ(T, ⊤) d :=
  ringHomEquiv Γ(T, ⊤) d

/-- Points of the universal coefficient spectrum are distinguished commutative
associative algebra structures over global sections with first basis vector as unit. -/
def schemeHomEquiv (T : Scheme) (d : ℕ+) :
    (T ⟶ baseScheme d) ≃ FreeDimAlgebra Γ(T, ⊤) d :=
  (schemeHomCoeff T d).trans (schemeHomFreeDimAlgebra T d)

/-- The algebra classified by a scheme morphism is reconstructed from its
classifying ring map on global sections. -/
theorem schemeHomEquiv_apply (T : Scheme) (d : ℕ+) (f : T ⟶ baseScheme d) :
    schemeHomEquiv T d f = ofRingHom (schemeHomCoeff T d f) := rfl

/-- The inverse point classification is the morphism determined by the
classifying ring map of the distinguished algebra. -/
theorem schemeHomEquiv_symm_apply (T : Scheme) (d : ℕ+)
    (m : FreeDimAlgebra Γ(T, ⊤) d) :
    (schemeHomEquiv T d).symm m = (schemeHomCoeff T d).symm (toRingHom m) := rfl

/-- Morphisms from an affine spectrum to the universal coefficient spectrum
classify distinguished algebra structures over its coordinate ring. -/
def specHomEquiv (R : Type) [CommRing R] (d : ℕ+) :
    (Spec (CommRingCat.of R) ⟶ baseScheme d) ≃ FreeDimAlgebra R d :=
  (Spec.homEquiv.trans
    ({ toFun := CommRingCat.Hom.hom
       invFun := CommRingCat.ofHom
       left_inv := CommRingCat.ofHom_hom
       right_inv := CommRingCat.hom_ofHom } :
      (CommRingCat.of (CoefficientRing d) ⟶ CommRingCat.of R) ≃
        (CoefficientRing d →+* R))).trans (ringHomEquiv R d)

end UniversalFiniteFreeAlgebra
