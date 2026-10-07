module

public import stacks_project.Chap92.Lemma_92_3_4_DirectLimit
public import stacks_project.Chap92.Lemma_92_6_1_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived functoriality of the cotangent complex after a derived-tensor quasi-isomorphism

If a commutative square of rings induces a quasi-isomorphism `B ⊗[A]^L A' = B'`, the
Section 92.6 functoriality map becomes an isomorphism
`L_{B/A} ⊗[B]^L B' ⟶ L_{B'/A'}` in `D(B')`.
-/

@[expose] public section

open CategoryTheory
open RingedSite.Cotangent.Functoriality

universe u

noncomputable section

namespace Algebra.CotangentComplex

variable {A B A' B' : CommRingCat.{u}}
variable {α : A ⟶ B} {ρ : A ⟶ A'} {β : A' ⟶ B'} {φ : B ⟶ B'}

/-- Ring-hom commutativity of a square of morphisms in `CommRingCat`. -/
theorem w_hom (sq : CommSq ρ α β φ) :
    β.hom.comp ρ.hom = φ.hom.comp α.hom :=
  sorry

/-- The derived functoriality map `L_{B/A} ⊗[B]^L B' ⟶ L_{B'/A'}` induced by a commutative
square of ring maps. -/
def mapDerived (sq : CommSq ρ α β φ) :
    DerivedCategory.Q.obj
      (((ModuleCat.extendScalars φ.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (RingHom.cotangentComplex α.hom)) ⟶
      DerivedCategory.Q.obj (RingHom.cotangentComplex β.hom) :=
  DerivedCategory.Q.map (map α.hom β.hom ρ.hom φ.hom (w_hom sq))

/-- Unfolding of `mapDerived` as `DerivedCategory.Q.map` of the cochain-level functoriality
map. -/
theorem mapDerived_eq (sq : CommSq ρ α β φ) :
    mapDerived sq =
      DerivedCategory.Q.map (map α.hom β.hom ρ.hom φ.hom (w_hom sq)) :=
  sorry

/-- Lemma 92.6.2. If the commutative square (92.6.0.1) induces a quasi-isomorphism
`B ⊗[A]^L A' = B'`, then the functoriality map induces an isomorphism
`L_{B/A} ⊗[B]^L B' ⟶ L_{B'/A'}` in `D(B')`. -/
@[stacks 08QQ]
theorem mapDerived_isIso (sq : CommSq ρ α β φ)
    (h : InducesDerivedTensorQuasiIso sq) :
    IsIso (mapDerived sq) :=
  sorry

end Algebra.CotangentComplex

