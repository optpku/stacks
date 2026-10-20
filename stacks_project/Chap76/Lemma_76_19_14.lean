module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap76.Remark_76_7_5_Glueing
public import stacks_project.Chap76.Lemma_76_15_14_Transitivity
public import stacks_project.Chap76.Lemma_76_19_2_FormallySmooth

/-!
# Short exactness and étale-local splitting of the two-unramified-morphisms sequence

If `i : Z ⟶ X` and `j : Z ⟶ Y` are formally unramified morphisms of algebraic
spaces over a scheme `S` and `f : X ⟶ Y` is formally smooth, the canonical
right-exact sequence of Lemma 76.15.14 is short exact and étale-locally split.
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

/-- The Lemma 76.15.14 complex splits after pullback along some covering family
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
              (Modules.pullback (U k).hom)).Splitting) :=
  sorry

/-- Lemma 76.19.14: Let `S` be a scheme. Let `i : Z ⟶ X` and `j : Z ⟶ Y` be
formally unramified morphisms of algebraic spaces over `S`, and let `f : X ⟶ Y`
be formally smooth, fitting in a commutative triangle. Then the canonical exact
sequence `0 ⟶ C_{Z/Y} ⟶ C_{Z/X} ⟶ i^* Ω_{X/Y} ⟶ 0` of Lemma 76.15.14 is short
exact and étale-locally split. Here `i` is `iX ≫ fX` and `j` is `iY ≫ fY`,
with `C_{Z/Y}` the conormal of `iY`, `C_{Z/X}` the conormal of `iX`, and
`i^* Ω_{X/Y}` the pullback of `Ω_{X/Y}` along `iX ≫ fX`; the arrows are
`projection` and `map`. -/
@[stacks 06BK]
theorem shortExact_and_etaleLocallySplit [FormallySmooth f] :
    (complex iX fX iY fY f sq).ShortExact ∧
      IsEtaleLocallySplit iX fX iY fY f sq :=
  sorry

/-- For a formally smooth morphism `f : X ⟶ Y` and formally unramified
morphisms `Z ⟶ X` and `Z ⟶ Y`, the Lemma 76.15.14 complex is short exact. -/
theorem shortExact [FormallySmooth f] :
    (complex iX fX iY fY f sq).ShortExact :=
  sorry

/-- For a formally smooth morphism `f : X ⟶ Y` and formally unramified
morphisms `Z ⟶ X` and `Z ⟶ Y`, the Lemma 76.15.14 complex is étale-locally
split. -/
theorem etaleLocallySplit [FormallySmooth f] :
    IsEtaleLocallySplit iX fX iY fY f sq :=
  sorry

/-- For a formally smooth morphism `f : X ⟶ Y`, the first arrow
`C_{Z/Y} ⟶ C_{Z/X}` of the Lemma 76.15.14 sequence is a monomorphism. -/
instance projection_mono [FormallySmooth f] :
    Mono (projection iX fX iY fY f sq) :=
  sorry

end Transitivity
end Differentials
end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
