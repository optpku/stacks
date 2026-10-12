/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import stacks_project.Chap67.Definition_67_40_1_Proper

/-!
# Compactifications of algebraic spaces

An algebraic space `X` over `B` has a compactification over `B` when the
structure morphism `f : X ⟶ B` factors as a quasi-compact open immersion into
an algebraic space proper over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space `X` over `B` has a compactification over `B` if the
structure morphism `f : X ⟶ B` factors as a quasi-compact open immersion
`ι : X ⟶ Xbar` followed by a proper morphism `p : Xbar ⟶ B`. -/
class HasCompactification {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) :
    Prop where
  /-- There is a quasi-compact open immersion into an algebraic space proper over
  `B` whose composite recovers `f`. -/
  exists_compactification :
    ∃ (Xbar : AlgebraicSpace S) (ι : X ⟶ Xbar) (p : Xbar ⟶ B),
      IsOpenImmersion ι ∧ QuasiCompact ι ∧ Proper p ∧ ι ≫ p = f

/-- A morphism has a compactification if and only if it factors as a
quasi-compact open immersion into an algebraic space proper over the target. -/
theorem hasCompactification_iff {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) :
    HasCompactification f ↔
      ∃ (Xbar : AlgebraicSpace S) (ι : X ⟶ Xbar) (p : Xbar ⟶ B),
        IsOpenImmersion ι ∧ QuasiCompact ι ∧ Proper p ∧ ι ≫ p = f :=
  sorry

namespace HasCompactification

/-- A morphism with a compactification factors as a quasi-compact open immersion
into an algebraic space proper over the target. -/
theorem spec {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [HasCompactification f] :
    ∃ (Xbar : AlgebraicSpace S) (ι : X ⟶ Xbar) (p : Xbar ⟶ B),
      IsOpenImmersion ι ∧ QuasiCompact ι ∧ Proper p ∧ ι ≫ p = f :=
  sorry

/-- A proper morphism is a compactification of itself, via the identity open
immersion. -/
instance of_proper {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Proper f] : HasCompactification f where
  exists_compactification :=
    ⟨X, 𝟙 X, f, inferInstance, inferInstance, inferInstance, Category.id_comp f⟩

end HasCompactification

end AlgebraicGeometry.AlgebraicSpace
