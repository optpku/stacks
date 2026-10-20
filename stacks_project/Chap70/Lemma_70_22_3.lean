/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.ValuativeCriterion.DVR
import StacksCheckRecall

/-!
# Refined Noetherian DVR valuative criterion for properness

A finite-type quasi-separated morphism of algebraic spaces into a locally
Noetherian target is proper as soon as every DVR valuative square whose
generic arrow factors through a dense finite-type morphism admits a unique
dotted lift.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion.DVR.Along

/- Lemma 70.22.3: Let `S` be a scheme. Let `f : X ⟶ Y` and `h : U ⟶ X` be
morphisms of algebraic spaces over `S`. Assume that `Y` is locally Noetherian,
that `f` and `h` are of finite type, that `f` is quasi-separated, and that the
image of `|h| : |U| ⟶ |X|` is dense in `|X|`. If given any commutative solid
diagram `Spec(K) ⟶ U ⟶ X` over `Spec(A) ⟶ Y` where `A` is a discrete valuation
ring with field of fractions `K`, there exists a unique dotted arrow making the
diagram commute, then `f` is proper. -/
@[stacks 0CMF]
#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Along.proper :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (f : X ⟶ Y) (h : U ⟶ X)
    [IsLocallyNoetherian Y] [FiniteType f] [FiniteType h] [QuasiSeparated f]
    [Dominant h] (h_valuative : ExistsUnique h f), Proper f)

end ValuativeCriterion.DVR.Along

end AlgebraicGeometry.AlgebraicSpace
