module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap75.Lemma_75_6_1_Pushforward

/-!
# Derived pushforward and quasicoherent coreflections on algebraic spaces

Restricted derived pushforward along a quasi-compact and quasi-separated morphism
of algebraic spaces commutes, up to natural isomorphism, with right adjoints to the
inclusions of derived modules having quasi-coherent cohomology.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- For a quasi-compact and quasi-separated morphism of algebraic spaces, restricted
derived pushforward after the source quasicoherent coreflection is naturally
isomorphic to ambient derived pushforward followed by the target quasicoherent
coreflection. -/
theorem pushforward_comp_rightAdjoint_isomorphic {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [(inclusion X).IsLeftAdjoint] [(inclusion Y).IsLeftAdjoint] :
    IsIsomorphic ((inclusion X).rightAdjoint ⋙ pushforward f)
      (Modules.pushforwardDerived f ⋙ (inclusion Y).rightAdjoint) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
