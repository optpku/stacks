module

public import stacks_project.Chap98.Lemma_98_21_6_Along
public import stacks_project.Chap98.Lemma_98_21_6_Sequence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness of Inf and T for a 2-fibre product

If `p : X ⟶ Y` and `q : Z ⟶ Y` are 1-morphisms of categories fibred in
groupoids over `(Sch/S)_fppf` and `X`, `Y`, `Z` satisfy (RS*), then at any
fibre object `w` of `W = X ×_Y Z` over an `S`-algebra `A` the six-term sequence
of `A`-modules `Inf_w(M)`, `Inf_x(M) × Inf_z(M)`, `Inf_y(M)`, `T_w(M)`,
`T_x(M) × T_z(M)`, `T_y(M)` is exact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Lemma 98.21.6. Let `S` be a scheme. Let `p : X ⟶ Y` and `q : Z ⟶ Y` be
1-morphisms of categories fibred in groupoids over `(Sch/S)_fppf`. Assume `X`,
`Y`, `Z` satisfy (RS*). Let `A` be an `S`-algebra and let `w` be an object of
`W = X ×_Y Z` over `A`. Denote `x`, `y`, `z` the objects of `X`, `Y`, `Z`
obtained from `w`. For any `A`-module `M` the sequence
`0 ⟶ Inf_w(M) ⟶ Inf_x(M) × Inf_z(M) ⟶ Inf_y(M) ⟶ T_w(M) ⟶ T_x(M) × T_z(M) ⟶ T_y(M)`
of `A`-modules is exact. Horizontal maps come from 1-morphism functoriality of
`Inf` and `T`; the connecting map `Inf_y(M) ⟶ T_w(M)` inserts an infinitesimal
automorphism of the trivial deformation of `y` into the 2-fibre-product
comparison of the trivial deformations of `x` and `z`. -/
@[stacks 0DNN]
theorem infTangentSequence_exact {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Z ⟶ Y)
    [HasStrongRimSchlessinger X] [HasStrongRimSchlessinger Y]
    [HasStrongRimSchlessinger Z] {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) :
    Function.Injective (infProd p q w M) ∧
      Function.Exact (infProd p q w M) (infDiff p q w M) ∧
      Function.Exact (infDiff p q w M) (connecting p q w M) ∧
      Function.Exact (connecting p q w M) (tangentProd p q w M) ∧
      Function.Exact (tangentProd p q w M) (tangentDiff p q w M) := sorry

end AlgebraicGeometry.GroupoidsOver
