module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import ReasLib.AlgebraicGeometry.Scheme.UniversalFiniteFree
public import stacks_project.Chap97.«97_13_0_1_Over»
public import stacks_project.Chap97.«97_13_0_2_FreeDimAlgebra»

/-!
# T-points of the universal finite free algebra scheme

Zariski localization of the representing property of `CoefficientRing d` identifies
morphisms `T ⟶ baseScheme d` with free `d`-dimensional algebras over `Γ(T, ⊤)`.
-/

@[expose] public section

open AlgebraicGeometry Opposite
open CategoryTheory hiding Over
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace UniversalFiniteFreeAlgebra

/-- The underlying ring homomorphism of a morphism in `CommRingCat`. -/
def commRingHomEquiv (R S : Type u) [CommRing R] [CommRing S] :
    (CommRingCat.of R ⟶ CommRingCat.of S) ≃ (R →+* S) where
  toFun f := CommRingCat.Hom.hom f
  invFun := CommRingCat.ofHom
  left_inv := CommRingCat.ofHom_hom
  right_inv := CommRingCat.hom_ofHom

/-- Morphisms `T ⟶ baseScheme d` correspond to ring maps out of the universal
coefficient ring into global sections. -/
def schemeHomCoeff (T : Scheme) (d : ℕ+) :
    (T ⟶ baseScheme d) ≃ (CoefficientRing d →+* Γ(T, ⊤)) where
  toFun f :=
    (CategoryTheory.opEquiv (Scheme.Γ.rightOp.obj T)
        (op (CommRingCat.of (CoefficientRing d)))
        ((ΓSpec.adjunction.homEquiv T
            (op (CommRingCat.of (CoefficientRing d)))).symm f)).hom
  invFun ψ :=
    T.toSpecΓ ≫
      Spec.map
        (CommRingCat.ofHom ψ : CommRingCat.of (CoefficientRing d) ⟶ Γ(T, ⊤))
  left_inv := sorry
  right_inv := sorry

/-- The free `d`-dimensional algebra with the same multiplication as `m`. -/
def toFreeDimAlgebra {R : Type u} [CommRing R] {d : ℕ+} (m : Over R d) :
    FreeDimAlgebra R d where
  mul := m.mul
  mul_assoc := m.mul_assoc
  mul_comm := m.mul_comm
  one_mul := m.one_mul

/-- Rebuild the packaged `Over` datum from a free `d`-dimensional algebra. -/
def ofFreeDimAlgebra {R : Type u} [CommRing R] {d : ℕ+} (m : FreeDimAlgebra R d) :
    Over R d where
  mul := m.mul
  mul_assoc := m.mul_assoc
  mul_comm := m.mul_comm
  one_mul := m.one_mul

/-- `Over R d` is the same datum as `FreeDimAlgebra R d`. -/
def overEquivFreeDimAlgebra (R : Type u) [CommRing R] (d : ℕ+) :
    Over R d ≃ FreeDimAlgebra R d where
  toFun := toFreeDimAlgebra
  invFun := ofFreeDimAlgebra
  left_inv := sorry
  right_inv := sorry

/-- Classifying maps `CoefficientRing d →+* Γ(T, ⊤)` correspond to free
`d`-dimensional algebras over global sections. -/
def schemeHomFreeDimAlgebra (T : Scheme) (d : ℕ+) :
    (CoefficientRing d →+* Γ(T, ⊤)) ≃ FreeDimAlgebra Γ(T, ⊤) d :=
  (Over.ringHomEquiv Γ(T, ⊤) d).trans (overEquivFreeDimAlgebra Γ(T, ⊤) d)

/-- 97.13.0.1: let `d ≥ 1` and let `X = baseScheme d`. For every scheme `T`,
the `T`-points of `X` are the free `d`-dimensional algebras `m` over `Γ(T, ⊤)`. -/
@[stacks 05YM]
def schemeHomEquiv (T : Scheme) (d : ℕ+) :
    (T ⟶ baseScheme d) ≃ FreeDimAlgebra Γ(T, ⊤) d :=
  (schemeHomCoeff T d).trans (schemeHomFreeDimAlgebra T d)

/-- `schemeHomEquiv` sends a morphism to the free `d`-dimensional algebra obtained
from its classifying map on global sections. -/
theorem schemeHomEquiv_apply (T : Scheme) (d : ℕ+) (f : T ⟶ baseScheme d) :
    schemeHomEquiv T d f = toFreeDimAlgebra (Over.ofRingHom (schemeHomCoeff T d f)) :=
  sorry

/-- The inverse of `schemeHomEquiv` sends a free `d`-dimensional algebra to the
morphism classified by its universal coefficient map. -/
theorem schemeHomEquiv_symm_apply (T : Scheme) (d : ℕ+)
    (m : FreeDimAlgebra Γ(T, ⊤) d) :
    (schemeHomEquiv T d).symm m =
      (schemeHomCoeff T d).symm (Over.toRingHom (ofFreeDimAlgebra m)) :=
  sorry

/-- Affine case of the previous setup: for `T = Spec(R)`, morphisms
`T ⟶ baseScheme d` recover free `d`-dimensional algebras over `R`. -/
def specHomEquiv (R : Type) [CommRing R] (d : ℕ+) :
    (Spec (CommRingCat.of R) ⟶ baseScheme d) ≃ FreeDimAlgebra R d :=
  (Spec.homEquiv.trans (commRingHomEquiv (CoefficientRing d) R)).trans
    ((Over.ringHomEquiv R d).trans (overEquivFreeDimAlgebra R d))

end UniversalFiniteFreeAlgebra
