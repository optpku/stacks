/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Compactifications of algebraic spaces

An algebraic space `X` over `B` has a compactification over `B` when its
structure morphism factors through a quasi-compact open immersion followed by
a proper morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space morphism has a compactification when it factors through
a quasi-compact open immersion followed by a proper morphism. -/
class HasCompactification {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) :
    Prop where
  /-- A compactification consists of a quasi-compact open immersion into an
  algebraic space proper over the target, whose composite is the given map. -/
  exists_compactification :
    ∃ (Xbar : AlgebraicSpace S) (ι : X ⟶ Xbar) (p : Xbar ⟶ B),
      IsOpenImmersion ι ∧ QuasiCompact ι ∧ Proper p ∧ ι ≫ p = f

/-- A morphism has a compactification exactly when it admits the corresponding
factorization through a quasi-compact open immersion and a proper morphism. -/
theorem hasCompactification_iff {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) :
    HasCompactification f ↔
      ∃ (Xbar : AlgebraicSpace S) (ι : X ⟶ Xbar) (p : Xbar ⟶ B),
        IsOpenImmersion ι ∧ QuasiCompact ι ∧ Proper p ∧ ι ≫ p = f :=
  sorry

namespace HasCompactification

/-- A compactifiable morphism admits its compactifying factorization. -/
theorem spec {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [HasCompactification f] :
    ∃ (Xbar : AlgebraicSpace S) (ι : X ⟶ Xbar) (p : Xbar ⟶ B),
      IsOpenImmersion ι ∧ QuasiCompact ι ∧ Proper p ∧ ι ≫ p = f :=
  sorry

/-- A proper morphism is compactifiable via its identity open immersion. -/
instance of_proper {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Proper f] : HasCompactification f where
  exists_compactification :=
    ⟨X, 𝟙 X, f, inferInstance, inferInstance, inferInstance, Category.id_comp f⟩

/-- A separated finite-type morphism to a quasi-compact, absolutely
quasi-separated algebraic space has a compactification. -/
instance of_finiteType {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiCompact B] [IsAbsolutelyQuasiSeparated B]
    (f : X ⟶ B) [FiniteType f] [Separated f] :
    HasCompactification f :=
  sorry

end HasCompactification

end AlgebraicGeometry.AlgebraicSpace
