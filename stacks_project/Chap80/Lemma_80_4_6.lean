/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.LocallySurjective
import StacksCheckRecall

/-!
# Surjectivity of flat, locally of finite presentation morphisms of sheaves

A morphism of fppf sheaves on schemes over `S` that is representable by
algebraic spaces and whose base changes along Yoneda sections are flat,
locally of finite presentation, and surjective is locally surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 80.4.6: if `S` is a scheme and `a : F ⟶ G` is a morphism of fppf sheaves
of sets on `Over S` that is representable by algebraic spaces and whose base
changes along Yoneda sections are flat, locally of finite presentation, and
surjective as morphisms of algebraic spaces, then `a` is surjective as a map of
sheaves, in the sense of `Presheaf.IsLocallySurjective` on
`Scheme.fppfTopology.over S`. -/
@[stacks 04S1] #check
  (AlgebraicGeometry.AlgebraicSpace.isLocallySurjective_of_flat_locallyOfFinitePresentation_surjective :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G),
      Presheaf.IsSheaf (Scheme.fppfTopology.over S) F →
      Presheaf.IsSheaf (Scheme.fppfTopology.over S) G →
      ∀ (ha : representableByAlgebraicSpaces a),
        (∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), Flat (ha.pullbackHom ξ)) →
        (∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G),
          LocallyOfFinitePresentation (ha.pullbackHom ξ)) →
        (∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), Surjective (ha.pullbackHom ξ)) →
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) a)

end AlgebraicGeometry.AlgebraicSpace
