/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyLifting

/-!
# Formally smooth morphisms of algebraic spaces

A morphism of algebraic spaces is formally smooth when its induced transformation
of functors of points is formally smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is formally smooth when its induced transformation
of functors of points is formally smooth. -/
class FormallySmooth {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop where
  /-- The induced transformation of functors of points is formally smooth. -/
  ofFunctor : Scheme.Over.FormallySmooth f

/-- Formal smoothness of an algebraic-space morphism is equivalent to formal smoothness
of its induced transformation of functors of points. -/
theorem formallySmooth_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    FormallySmooth f ↔ Scheme.Over.FormallySmooth f :=
  sorry

namespace FormallySmooth

/-- A formally smooth transformation of functors of points induces a formally smooth
morphism of algebraic spaces. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Scheme.Over.FormallySmooth f) : FormallySmooth f :=
  sorry

/-- The induced transformation of functors of points of a formally smooth morphism is
formally smooth. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [FormallySmooth f] : Scheme.Over.FormallySmooth f :=
  sorry

/-- The identity morphism of an algebraic space is formally smooth. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    FormallySmooth (𝟙 X) :=
  sorry

/-- A formally smooth morphism of algebraic spaces induces a formally smooth
transformation of functors of points. -/
instance toSchemeOver {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [FormallySmooth f] : Scheme.Over.FormallySmooth f :=
  sorry

end FormallySmooth

end AlgebraicGeometry.AlgebraicSpace
