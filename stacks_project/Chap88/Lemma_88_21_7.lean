/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_21_1
public import stacks_project.Chap88.Definition_88_20_1_Etale

/-!
# Étale covering morphisms are rig-surjective

A morphism of locally Noetherian formal algebraic spaces that is representable
by algebraic spaces, étale, and surjective is rig-surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- An étale morphism of functors of points is locally of finite type. -/
instance locallyOfFiniteType_of_etale {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) [Etale f] : LocallyOfFiniteType f :=
  sorry

namespace RigSurjective

/-- Lemma 88.21.7: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
locally Noetherian formal algebraic spaces which is representable by algebraic
spaces, étale, and surjective. Then `f` is rig-surjective. -/
@[stacks 0AQU]
theorem of_etale {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [hf : Etale f]
    (h_surj : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.Surjective
        (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom hf.representable ξ)) :
    RigSurjective f :=
  sorry

end RigSurjective

end AlgebraicGeometry.FormalAlgebraicSpace
