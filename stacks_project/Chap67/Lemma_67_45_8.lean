module

public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_27_3_QuasiFinite

/-!
# Finite morphisms of algebraic spaces are quasi-finite
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace QuasiFinite

/-- Lemma 67.45.8: A finite morphism of algebraic spaces is quasi-finite. -/
@[stacks 04NY]
instance of_isFinite {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsFinite f] : QuasiFinite f :=
  sorry

end QuasiFinite

end AlgebraicGeometry.AlgebraicSpace
