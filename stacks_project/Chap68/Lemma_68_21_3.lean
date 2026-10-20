module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.GenericFiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.21.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`, locally of finite type, and let `y` be a
codimension-zero point of `Y`. The following are equivalent: the fibre over
`y` consists of codimension-zero points; `f` is quasi-finite at every point of
the fibre; and `f` is quasi-finite at every codimension-zero point of the
fibre. -/
@[stacks 0BBB] #check
  (AlgebraicGeometry.AlgebraicSpace.tfae_fiber_subset_codimZero_quasiFiniteAt :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFiniteType f] {y : Points Y},
      localRingDimAt y = 0 →
        List.TFAE
          [ Points.map f ⁻¹' {y} ⊆ setOf fun x : Points X ↦ localRingDimAt x = 0
          , ∀ x : Points X, Points.map f x = y → FiniteType.QuasiFiniteAt f x
          , ∀ x : Points X,
              localRingDimAt x = 0 → Points.map f x = y →
                FiniteType.QuasiFiniteAt f x ])

#check
  (AlgebraicGeometry.AlgebraicSpace.fiber_subset_codimZero_iff_quasiFiniteAt :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFiniteType f] {y : Points Y},
      localRingDimAt y = 0 →
        ((Points.map f ⁻¹' {y} ⊆ setOf fun x : Points X ↦ localRingDimAt x = 0) ↔
          ∀ x : Points X, Points.map f x = y → FiniteType.QuasiFiniteAt f x))

#check
  (AlgebraicGeometry.AlgebraicSpace.quasiFiniteAt_fiber_iff_quasiFiniteAt_codimZero :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFiniteType f] {y : Points Y},
      localRingDimAt y = 0 →
        ((∀ x : Points X, Points.map f x = y → FiniteType.QuasiFiniteAt f x) ↔
          ∀ x : Points X, localRingDimAt x = 0 → Points.map f x = y →
            FiniteType.QuasiFiniteAt f x))

end AlgebraicGeometry.AlgebraicSpace
