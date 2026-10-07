module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap75.Lemma_75_13_7_PseudoCoherent
public import stacks_project.Chap86.Remark_86_3_5_Finiteness

/-!
# Sheafy trace for proper morphisms of Noetherian algebraic spaces

For a proper morphism of Noetherian algebraic spaces, the sheafy-trace morphism
`Rf_* RHom(L, a(K)) ⟶ RHom(Rf_* L, K)` is an isomorphism when `L` is in
`D⁻_Coh` and `K` is in `D⁺_QCoh`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.MonoidalClosed
open CategoryTheory.Functor.LaxMonoidal
open DerivedCategory.TStructure

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- For a proper morphism of Noetherian algebraic spaces, the sheafy-trace morphism
is an isomorphism when `L` is bounded above with coherent cohomology and `K` is
bounded below. -/
theorem sheafyTrace_isIso_of_proper {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsNoetherian X] [IsNoetherian Y] [Proper f]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [Functor.LaxMonoidal (moduleDerivedPushforward f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y)
    (hL_minus : (t.minus : ObjectProperty (ModuleDerived X)) L.obj)
    (hL_coh : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) L.obj)
    (hK : K.obj.IsBoundedBelow) :
    IsIso (sheafyTrace f a adj L K) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
