/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.Differentials.Transitivity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth
import Mathlib.Tactic.CrossRefAttribute

/-!
# Short exactness and étale-local splitting of the two-unramified-morphisms sequence

If `i : Z ⟶ X` and `j : Z ⟶ Y` are formally unramified morphisms of algebraic
spaces over a scheme `S` and `f : X ⟶ Y` is formally smooth, the canonical
conormal transitivity sequence is short exact and étale-locally split.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
namespace Differentials
namespace Transitivity

variable {S : Scheme.{u}} {X Y Z ZX ZY : AlgebraicSpace S}
variable (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY) (fY : ZY ⟶ Y) (f : X ⟶ Y)
variable [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
variable [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)]
variable (sq : CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f)

/-- The canonical conormal transitivity complex splits after pullback along some covering family
in the small étale site of `Z`. -/
def IsEtaleLocallySplit : Prop :=
  ∃ (I : Type u) (U : I → smallEtaleSite Z),
    (smallEtaleTopology Z).CoversTop U ∧
      ∀ k : I, Nonempty (((complex iX fX iY fY f sq).map (Modules.pullback (U k).hom)).Splitting)

/-- Étale-local splitting of the two-unramified-morphisms complex is equivalent
to the existence of a covering family in `Z_étale` on which the pulled-back
complex admits a splitting. -/
theorem isEtaleLocallySplit_iff :
    IsEtaleLocallySplit iX fX iY fY f sq ↔
      ∃ (I : Type u) (U : I → smallEtaleSite Z),
        (smallEtaleTopology Z).CoversTop U ∧
          ∀ k : I, Nonempty (((complex iX fX iY fY f sq).map
              (Modules.pullback (U k).hom)).Splitting) := sorry

/-- For a commutative triangle of algebraic spaces over a scheme `S`, with
formally unramified morphisms `i : Z ⟶ X` and `j : Z ⟶ Y` and formally smooth
`f : X ⟶ Y`, the canonical sequence
`0 ⟶ C_{Z/Y} ⟶ C_{Z/X} ⟶ i^* Ω_{X/Y} ⟶ 0` is short exact and étale-locally split.
Here `i = iX ≫ fX` and `j = iY ≫ fY` are presented by universal first-order
thickenings, the conormal terms are `Hom.conormalSheaf iY` and `Hom.conormalSheaf iX`,
and the last term is the pullback of `Hom.relativeDifferentials f` along `iX ≫ fX`.
The canonical arrows are `projection` and `IsUniversalFirstOrder.Differentials.conormalMap`. -/
@[stacks 06BK]
theorem shortExact_and_etaleLocallySplit [FormallySmooth f] :
    (complex iX fX iY fY f sq).ShortExact ∧
      IsEtaleLocallySplit iX fX iY fY f sq := sorry

/-- For a formally smooth morphism `f : X ⟶ Y` and formally unramified
morphisms `Z ⟶ X` and `Z ⟶ Y`, the canonical conormal transitivity complex is short exact. -/
theorem shortExact [FormallySmooth f] :
    (complex iX fX iY fY f sq).ShortExact := sorry

/-- For a formally smooth morphism `f : X ⟶ Y` and formally unramified
morphisms `Z ⟶ X` and `Z ⟶ Y`, the canonical conormal transitivity complex is étale-locally
split. -/
theorem etaleLocallySplit [FormallySmooth f] :
    IsEtaleLocallySplit iX fX iY fY f sq := sorry

/-- For a formally smooth morphism `f : X ⟶ Y`, the first arrow
`C_{Z/Y} ⟶ C_{Z/X}` of the canonical conormal transitivity sequence is a monomorphism. -/
instance projection_mono [FormallySmooth f] :
    Mono (projection iX fX iY fY f sq) := sorry

end Transitivity
end Differentials
end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
