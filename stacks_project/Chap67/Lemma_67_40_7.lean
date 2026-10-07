module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_5_2_Surjective

/-!
# Cancellation of universal closedness along a surjection

If a morphism of algebraic spaces over a base is surjective and the composite
to the base is universally closed, then the second factor is universally
closed. In particular, a separated finite type second factor is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UniversallyClosed

/-- Lemma 67.40.7 (1): if `f : X ⟶ Y` is a surjective morphism of algebraic
spaces over `B` and `X` is universally closed over `B`, then `Y` is
universally closed over `B`. -/
@[stacks 08AJ]
theorem of_comp_surjective {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ B) [UniversallyClosed (f ≫ g)] [Surjective f] :
    UniversallyClosed g :=
  sorry

end UniversallyClosed

namespace Proper

/-- Lemma 67.40.7 (2): if `f : X ⟶ Y` is a surjective morphism of algebraic
spaces over `B`, `X` is universally closed over `B`, and `Y` is separated and
of finite type over `B`, then `Y` is proper over `B`. -/
@[stacks 08AJ]
theorem of_comp_surjective {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ B) [UniversallyClosed (f ≫ g)] [Surjective f]
    [Separated g] [FiniteType g] : Proper g :=
  sorry

end Proper

end AlgebraicGeometry.AlgebraicSpace
