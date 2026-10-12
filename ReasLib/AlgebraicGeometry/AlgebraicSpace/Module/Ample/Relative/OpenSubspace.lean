/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace

/-!
# Characterizing open subspace for relative ampleness

A proper morphism of algebraic spaces and an invertible module on the source
admit an open subspace of the target through which a test morphism factors
if and only if the pulled-back module is relatively ample on the base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativelyAmple

/-- Let `S` be a scheme, let `f : X ⟶ Y` be a proper morphism of algebraic spaces
over `S`, and let `L` be an invertible object of `X.Modules`. There exists an
open subspace `V` of `Y` such that a morphism `g : Y' ⟶ Y` of algebraic spaces
factors through `V` if and only if the pullback of `L` along `pullback.fst f g`
is relatively ample on `pullback.snd f g`. -/
theorem exists_openSubspace_factorsThrough_iff
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    (L : X.Modules) [isInvertibleObject L] :
    ∃ V : OpenSubspace Y, ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y),
      (∃ χ : Y' ⟶ V.X, χ ≫ V.ι = g) ↔
        RelativelyAmple (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj L) :=
  sorry

/-- If two open subspaces of the target of a proper morphism of algebraic spaces
are characterized by relative ampleness of pullbacks of a given invertible
module, then they are unique as subobjects: there is a unique morphism over the
target between their underlying algebraic spaces. -/
theorem openSubspace_unique
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    (L : X.Modules) [isInvertibleObject L] (V W : OpenSubspace Y)
    (hV : ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y),
      (∃ χ : Y' ⟶ V.X, χ ≫ V.ι = g) ↔
        RelativelyAmple (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj L))
    (hW : ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y),
      (∃ χ : Y' ⟶ W.X, χ ≫ W.ι = g) ↔
        RelativelyAmple (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj L)) :
    ∃! χ : V.X ⟶ W.X, χ ≫ W.ι = V.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativelyAmple
