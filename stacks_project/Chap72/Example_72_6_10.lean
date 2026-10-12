/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap72.Example_72_6_10_ClassGroup
public import ReasLib.Topology.KrullDimension.Local
import StacksCheckRecall

/-!
# Example 72.6.10

The affine-line involution space is smooth over `k`, Noetherian and integral of
dimension one, and has Weil divisor class group `ℤ/2ℤ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

/-- The étale-square smoothness criterion for the structure morphism `toBase`:
every commutative square with étale vertical arrows from schemes has smooth
top arrow. This is not representable smoothness of `toBase`. -/
def isSmoothOverBase (k : Type u) [Field k] : Prop :=
  ∀ {U V : Over (base k)}
    (a : (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj U ⟶ sheafOfPoints k)
    (b : (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj V ⟶
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (Over.mk (𝟙 (base k))))
    (h : U ⟶ V),
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} a.hom →
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} b.hom →
        a ≫ toBase k =
            (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map h ≫ b →
          AlgebraicGeometry.Smooth h.left

/-- Example 72.6.10 (1): the algebraic space `X` is smooth over the field `k`.
Smoothness is the étale-square criterion of `AlgebraicSpace.Smooth`: every
commutative square with étale vertical arrows from schemes has smooth top
arrow. This is not representable smoothness of `toBase`. -/
@[stacks 0ENT]
theorem smooth_toBase (k : Type u) [Field k] [NeZero (2 : k)] :
    isSmoothOverBase k :=
  sorry

/- Example 72.6.10 (2): there is a universal homeomorphism `X ⟶ 𝔸¹_k = Spec(k[t])`. -/
@[stacks 0ENT] #check universalHomeomorphism_toAffineLine

/- Example 72.6.10 (3): the map `X ⟶ 𝔸¹_k` is an isomorphism over `𝔸¹_k \ {0}`. -/
@[stacks 0ENT] #check isIso_over_punctured

/-- Example 72.6.10 (4): `X` is Noetherian. In this sheaf encoding that means the
affine-line atlas is a Noetherian scheme and the diagonal of `X` is
representably quasi-compact. -/
@[stacks 0ENT]
theorem isNoetherian (k : Type u) [Field k] [NeZero (2 : k)] :
    AlgebraicGeometry.IsNoetherian (cover k).left ∧
      (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
        (diag (sheafOfPoints k).obj) :=
  sorry

/-- Example 72.6.10 (5): `X` is integral in the sense of Definition 72.4.1: it is
reduced, decent, and irreducible. The affine-line atlas is an integral scheme,
and the quasi-compact diagonal of `X` is the QS/decent witness. -/
@[stacks 0ENT]
theorem isIntegral (k : Type u) [Field k] [NeZero (2 : k)] :
    AlgebraicGeometry.IsIntegral (cover k).left ∧
      (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
        (diag (sheafOfPoints k).obj) :=
  sorry

/-- The étale-local dimension of `X`, as the supremum of local topological Krull
dimensions along étale scheme charts of `sheafOfPoints`. -/
def dimension (k : Type u) [Field k] : WithBot ℕ∞ :=
  ⨆ (U : Over (base k))
    (f : (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj U ⟶ sheafOfPoints k)
    (hf : (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} f.hom)
    (u : U.left), topologicalKrullDimAt u

/-- Example 72.6.10 (6): `dim(X) = 1` as an étale-local dimension. -/
@[stacks 0ENT]
theorem dimension_eq_one (k : Type u) [Field k] [NeZero (2 : k)] :
    dimension k = 1 :=
  sorry

/- Example 72.6.10 (7): since `dim(X) = 1`, the prime divisors of `X` are the closed
points of `X`. Along the universal homeomorphism `toAffineLine` these transport
to the closed points of `𝔸¹_k`, equivalently the generic points of prime
divisors of `𝔸¹_k`. -/
@[stacks 0ENT] #check closedPoint_iff_exists_primeDivisor

/- Example 72.6.10 (8): there is a unique closed point `x ∈ |X|` lying over `0 ∈ 𝔸¹_k`. -/
@[stacks 0ENT] #check unique_point_over_origin

/-- Example 72.6.10 (9): the classes in `Cl(X)` of closed points different from `x` are
zero. -/
@[stacks 0ENT]
theorem class_eq_zero_of_ne_origin (k : Type u) [Field k] [NeZero (2 : k)]
    {Z : AlgebraicGeometry.PrimeDivisor (cover k).left}
    (hZ : Z ≠ originPrimeDivisor k) :
    classGroupMk k (primeWeilDivisor k Z) = 0 :=
  sorry

/-- Example 72.6.10 (10): the divisor of `t` on `X` is `2[x]`. -/
@[stacks 0ENT]
theorem principalWeilDivisor_coordinate (k : Type u) [Field k] [NeZero (2 : k)] :
    principalWeilDivisor k (coordinate k) = 2 • originWeilDivisor k :=
  sorry

/- Example 72.6.10 (11): `Cl(X) = ℤ/2ℤ`. -/
@[stacks 0ENT] #check classGroupEquivZMod

end AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution
