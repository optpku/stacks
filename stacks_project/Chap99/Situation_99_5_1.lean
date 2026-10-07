module

public import stacks_project.Chap99.Situation_99_5_1_Fiber
public import stacks_project.Chap99.Situation_99_5_1_Category

/-!
# The stack of coherent sheaves on a relative algebraic space

Situation 99.5.1 introduces the category of finitely presented quasi-coherent
modules with proper support on the fibres of a finite-presentation morphism
of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack (Obj)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Situation 99.5.1: for a finite-presentation morphism `f : X ⟶ B` of algebraic
spaces over a scheme `S`, `CohStack f` is the category of triples `(T, g, F)`
where `T` is a scheme over `S`, `g : T ⟶ B` is a morphism over `S`, and setting
`X_T = T ×_B X`, the sheaf `F` is a quasi-coherent `𝒪_{X_T}`-module of finite
presentation, flat over `T`, with support proper over `T`. A morphism
`(T, g, F) ⟶ (T', g', F')` is a pair `(h, φ)` where `h : T ⟶ T'` is a morphism
of schemes over `B` and `φ : (h')^* F' ≅ F` is an isomorphism of `𝒪_{X_T}`-modules,
where `h' : X_T ⟶ X_{T'}` is the base change of `h`. -/
@[stacks 08KB]
abbrev CohStack (f : X ⟶ B) [FinitePresentation f] :=
  _root_.AlgebraicGeometry.AlgebraicSpace.CohStack.Obj f

end AlgebraicGeometry.AlgebraicSpace
