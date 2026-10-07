module

public import Mathlib.Algebra.Algebra.Hom
public import stacks_project.Chap82.Definition_82_26_2_ChowCohomology

/-!
# Pullback of Chow cohomology of algebraic spaces

A morphism of good algebraic spaces over `B` induces a contravariant
`ℤ`-algebra map on Chow cohomology by reindexing identity cap families
along the test composition `X' ⟶ X ⟶ Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChowCohomology

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]

section Restrict

variable {X Y : AlgebraicSpace S} (pY : Y ⟶ B) (f : X ⟶ Y)
  [QuasiSeparated pY] [LocallyOfFiniteType pY]
  [QuasiSeparated (f ≫ pY)] [LocallyOfFiniteType (f ≫ pY)]

/-- Quasi-separation of a good test over `X` transports along associativity to
the reindexed test over `Y`. -/
instance instQuasiSeparated_restrictTest {X' : AlgebraicSpace S} (h : X' ⟶ X)
    [QuasiSeparated (h ≫ (f ≫ pY))] :
    QuasiSeparated ((h ≫ f) ≫ pY) :=
  sorry

/-- Local finite type of a good test over `X` transports along associativity to
the reindexed test over `Y`. -/
instance instLocallyOfFiniteType_restrictTest {X' : AlgebraicSpace S}
    (h : X' ⟶ X) [LocallyOfFiniteType (h ≫ (f ≫ pY))] :
    LocallyOfFiniteType ((h ≫ f) ≫ pY) :=
  sorry

/-- Restriction of a homogeneous identity class along `f` reindexes tests by
postcomposition with `f`. -/
def restrictCap (n : ℤ) (c : degree δ pY n) : CapFamily δ (f ≫ pY) n :=
  fun {X'} (h : X' ⟶ X)
      [QuasiSeparated (h ≫ (f ≫ pY))] [LocallyOfFiniteType (h ≫ (f ≫ pY))]
      (k : ℤ) ↦
    c.cap (h ≫ f) k

/-- Homogeneous restriction evaluates by viewing a test over `X` as a test over
`Y` via `h ≫ f`. -/
theorem restrictCap_apply (n : ℤ) (c : degree δ pY n)
    {X' : AlgebraicSpace S} (h : X' ⟶ X)
    [QuasiSeparated (h ≫ (f ≫ pY))] [LocallyOfFiniteType (h ≫ (f ≫ pY))]
    (k : ℤ) :
    restrictCap δ pY f n c h k = c.cap (h ≫ f) k :=
  sorry

/-- Restricted cap families remain compatible with proper pushforward. -/
theorem restrictCap_map_proper (n : ℤ) (c : degree δ pY n) :
    CompatibleWithProperPushforward δ (f ≫ pY) (restrictCap δ pY f n c) :=
  sorry

/-- Restricted cap families remain compatible with flat pullback. -/
theorem restrictCap_pullback_flat (n : ℤ) (c : degree δ pY n) :
    CompatibleWithFlatPullback δ (f ≫ pY) (restrictCap δ pY f n c) :=
  sorry

/-- Restricted cap families remain compatible with Gysin pullback. -/
theorem restrictCap_gysin_cartier (n : ℤ) (c : degree δ pY n) :
    CompatibleWithCartierGysin δ (f ≫ pY) (restrictCap δ pY f n c) :=
  sorry

/-- Additive homogeneous restriction of identity classes along `f`. -/
def restrictDegree (n : ℤ) : degree δ pY n →+ degree δ (f ≫ pY) n where
  toFun c :=
    ofCap δ (f ≫ pY) (restrictCap δ pY f n c)
      (restrictCap_map_proper δ pY f n c)
      (restrictCap_pullback_flat δ pY f n c)
      (restrictCap_gysin_cartier δ pY f n c)
  map_zero' := sorry
  map_add' := sorry

/-- Homogeneous restriction is `ofCap` of the reindexed cap family. -/
theorem restrictDegree_apply (n : ℤ) (c : degree δ pY n) :
    restrictDegree δ pY f n c =
      ofCap δ (f ≫ pY) (restrictCap δ pY f n c)
        (restrictCap_map_proper δ pY f n c)
        (restrictCap_pullback_flat δ pY f n c)
        (restrictCap_gysin_cartier δ pY f n c) :=
  sorry

/-- Homogeneous restriction sends the graded unit to the unit of Chow
cohomology. -/
theorem restrictOne :
    ((DirectSum.of (degree δ (f ≫ pY)) 0).comp (restrictDegree δ pY f 0))
        (GradedMonoid.GOne.one : degree δ pY 0) =
      (1 : ring δ (f ≫ pY)) :=
  sorry

/-- Homogeneous restriction preserves the product of identity classes. -/
theorem restrictMul {i j : ℤ} (a : degree δ pY i) (b : degree δ pY j) :
    ((DirectSum.of (degree δ (f ≫ pY)) (i + j)).comp
        (restrictDegree δ pY f (i + j))) (GradedMonoid.GMul.mul a b) =
      ((DirectSum.of (degree δ (f ≫ pY)) i).comp (restrictDegree δ pY f i)) a *
        ((DirectSum.of (degree δ (f ≫ pY)) j).comp (restrictDegree δ pY f j)) b :=
  sorry

/-- The canonical contravariant `ℤ`-algebra map `A⁎(Y) → A⁎(X)` induced by a
morphism of good algebraic spaces over `B`. -/
def restrict : ring δ pY →ₐ[ℤ] ring δ (f ≫ pY) :=
  (DirectSum.toSemiring
    (fun n ↦ (DirectSum.of (degree δ (f ≫ pY)) n).comp (restrictDegree δ pY f n))
    (restrictOne δ pY f) (restrictMul δ pY f)).toIntAlgHom

/-- Restriction of a homogeneous class is homogeneous restriction. -/
theorem restrict_of (n : ℤ) (c : degree δ pY n) :
    restrict δ pY f (DirectSum.of (degree δ pY) n c) =
      DirectSum.of (degree δ (f ≫ pY)) n (restrictDegree δ pY f n c) :=
  sorry

/-- The restricted class `f⁎ c` acts on a good test `h : X' ⟶ X` by the original
class `c` on `h ≫ f : X' ⟶ Y`. -/
theorem restrict_apply (n : ℤ) (c : degree δ pY n)
    {X' : AlgebraicSpace S} (h : X' ⟶ X)
    [QuasiSeparated (h ≫ (f ≫ pY))] [LocallyOfFiniteType (h ≫ (f ≫ pY))]
    (k : ℤ) :
    (restrictDegree δ pY f n c).cap h k = c.cap (h ≫ f) k :=
  sorry

end Restrict

/-- Restriction along an identity morphism is the identity algebra
homomorphism. -/
theorem restrict_id {Y : AlgebraicSpace S} (pY : Y ⟶ B)
    [QuasiSeparated pY] [LocallyOfFiniteType pY]
    [QuasiSeparated (𝟙 Y ≫ pY)] [LocallyOfFiniteType (𝟙 Y ≫ pY)] :
    restrict δ pY (𝟙 Y) = AlgHom.id ℤ (ring δ pY) :=
  sorry

/-- Chow-cohomology restriction is contravariantly functorial under
composition. -/
theorem restrict_comp {X Y Z : AlgebraicSpace S}
    (pZ : Z ⟶ B) (g : Y ⟶ Z) (f : X ⟶ Y)
    [QuasiSeparated pZ] [LocallyOfFiniteType pZ]
    [QuasiSeparated (g ≫ pZ)] [LocallyOfFiniteType (g ≫ pZ)]
    [QuasiSeparated ((f ≫ g) ≫ pZ)] [LocallyOfFiniteType ((f ≫ g) ≫ pZ)]
    [QuasiSeparated (f ≫ (g ≫ pZ))] [LocallyOfFiniteType (f ≫ (g ≫ pZ))] :
    restrict δ pZ (f ≫ g) = (restrict δ (g ≫ pZ) f).comp (restrict δ pZ g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ChowCohomology
