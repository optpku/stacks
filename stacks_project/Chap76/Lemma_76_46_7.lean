/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap76.Definition_76_46_1_PseudoCoherent

/-!
# Pseudo-coherent morphisms over locally Noetherian algebraic spaces

A morphism of algebraic spaces into a locally Noetherian target is
pseudo-coherent if and only if it is locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace PseudoCoherent

/-- Lemma 76.46.7: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `Y` is locally Noetherian, then `f` is
pseudo-coherent if and only if `f` is locally of finite type. -/
@[stacks 06BX]
theorem iff_locallyOfFiniteType {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsLocallyNoetherian Y] :
    PseudoCoherent f ↔ LocallyOfFiniteType f :=
  sorry

end PseudoCoherent

end AlgebraicGeometry.AlgebraicSpace
