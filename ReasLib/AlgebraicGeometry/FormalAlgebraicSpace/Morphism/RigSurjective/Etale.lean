/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.Etale.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Étale surjective morphisms are rig-surjective

An étale morphism between locally Noetherian formal algebraic spaces is
rig-surjective if every scheme-valued Yoneda pullback is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective

/-- An étale morphism between locally Noetherian formal algebraic spaces with
surjective scheme-valued Yoneda pullbacks is rig-surjective. -/
theorem of_etale {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [hf : Etale f]
    (h_surj : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.Surjective
        (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom hf.representable ξ)) :
    RigSurjective f :=
  sorry

/-- An étale morphism between locally Noetherian formal algebraic spaces is
rig-surjective when surjectivity of every scheme-valued Yoneda pullback is
available through inference. -/
instance of_etaleSurjectivePullbacks {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [hf : Etale f]
    [h_surj : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.Surjective
        (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom hf.representable ξ)] :
    RigSurjective f :=
  of_etale f h_surj

end AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective
