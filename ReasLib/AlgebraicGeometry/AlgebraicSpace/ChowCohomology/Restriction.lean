/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Hom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowCohomology.GradedRing

/-!
# Restriction of operational Chow cohomology of algebraic spaces

A morphism of good algebraic spaces over `B` induces a contravariant
`ℤ`-algebra map on operational Chow cohomology by reindexing cap families
along the test composition `X' ⟶ X ⟶ Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.OperationalChow

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
    QuasiSeparated ((h ≫ f) ≫ pY) := by
  simpa only [Category.assoc] using
    (inferInstance : QuasiSeparated (h ≫ (f ≫ pY)))

/-- Local finite type of a good test over `X` transports along associativity to
the reindexed test over `Y`. -/
instance instLocallyOfFiniteType_restrictTest {X' : AlgebraicSpace S}
    (h : X' ⟶ X) [LocallyOfFiniteType (h ≫ (f ≫ pY))] :
    LocallyOfFiniteType ((h ≫ f) ≫ pY) := by
  simpa only [Category.assoc] using
    (inferInstance : LocallyOfFiniteType (h ≫ (f ≫ pY)))

/-- Restriction of a homogeneous operational class along `f` reindexes tests by
postcomposition with `f`. -/
def restrictCap (n : ℤ) (c : Graded δ pY n) : CapFamily δ (f ≫ pY) n :=
  fun {X'} (h : X' ⟶ X)
      [QuasiSeparated (h ≫ (f ≫ pY))] [LocallyOfFiniteType (h ≫ (f ≫ pY))]
      (k : ℤ) ↦
    Graded.cap δ pY c (h ≫ f) k

/-- Homogeneous restriction evaluates by viewing a test over `X` as a test over
`Y` via `h ≫ f`. -/
theorem restrictCap_apply (n : ℤ) (c : Graded δ pY n)
    {X' : AlgebraicSpace S} (h : X' ⟶ X)
    [QuasiSeparated (h ≫ (f ≫ pY))] [LocallyOfFiniteType (h ≫ (f ≫ pY))]
    (k : ℤ) :
    restrictCap δ pY f n c h k = Graded.cap δ pY c (h ≫ f) k :=
  rfl

/-- Restricted cap families remain compatible with proper pushforward. -/
theorem restrictCap_map_proper (n : ℤ) (c : Graded δ pY n) :
    CompatibleWithProperPushforward δ (f ≫ pY) (restrictCap δ pY f n c) := by
  intro X' X'' g h _ _ _ _ _ _ _ k α
  exact c.property.1 (g ≫ f) h k α

/-- Restricted cap families remain compatible with flat pullback. -/
theorem restrictCap_pullback_flat (n : ℤ) (c : Graded δ pY n) :
    CompatibleWithFlatPullback δ (f ≫ pY) (restrictCap δ pY f n c) := by
  intro X' X'' g h _ _ _ _ _ _ r _ _ k α
  letI : QuasiSeparated (h ≫ (g ≫ f) ≫ pY) :=
    inferInstanceAs (QuasiSeparated (h ≫ g ≫ (f ≫ pY)))
  letI : LocallyOfFiniteType (h ≫ (g ≫ f) ≫ pY) :=
    inferInstanceAs (LocallyOfFiniteType (h ≫ g ≫ (f ≫ pY)))
  exact c.property.2.1 (g ≫ f) h r k α

/-- Restricted cap families remain compatible with Gysin pullback. -/
theorem restrictCap_gysin_cartier (n : ℤ) (c : Graded δ pY n) :
    CompatibleWithCartierGysin δ (f ≫ pY) (restrictCap δ pY f n c) := by
  intro X' g _ _ L _ s _ _ k α
  exact c.property.2.2 (g ≫ f) L s k α

/-- Additive homogeneous restriction of operational classes along `f`. -/
def restrictDegree (n : ℤ) : Graded δ pY n →+ Graded δ (f ≫ pY) n where
  toFun c :=
    Graded.ofOperational δ (f ≫ pY)
      (ofCap δ (f ≫ pY) (restrictCap δ pY f n c)
        (restrictCap_map_proper δ pY f n c)
        (restrictCap_pullback_flat δ pY f n c)
        (restrictCap_gysin_cartier δ pY f n c))
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' := by
    intro a b
    apply Subtype.ext
    rfl

/-- Homogeneous restriction is the compatible graded family of the reindexed
cap action. -/
theorem restrictDegree_apply (n : ℤ) (c : Graded δ pY n) :
    restrictDegree δ pY f n c =
      Graded.ofOperational δ (f ≫ pY)
        (ofCap δ (f ≫ pY) (restrictCap δ pY f n c)
          (restrictCap_map_proper δ pY f n c)
          (restrictCap_pullback_flat δ pY f n c)
          (restrictCap_gysin_cartier δ pY f n c)) :=
  rfl

/-- Homogeneous restriction sends the graded unit to the unit of operational
Chow cohomology. -/
theorem restrictOne :
    ((DirectSum.of (Graded δ (f ≫ pY)) 0).comp (restrictDegree δ pY f 0))
        (GradedMonoid.GOne.one : Graded δ pY 0) =
      (1 : ring δ (f ≫ pY)) := by
  change DirectSum.of (Graded δ (f ≫ pY)) 0
      (restrictDegree δ pY f 0 (Graded.one δ pY)) =
    DirectSum.of (Graded δ (f ≫ pY)) 0 (Graded.one δ (f ≫ pY))
  apply congrArg (DirectSum.of (Graded δ (f ≫ pY)) 0)
  exact Subtype.ext rfl

/-- Homogeneous restriction preserves the product of operational classes. -/
theorem restrictMul {i j : ℤ} (a : Graded δ pY i) (b : Graded δ pY j) :
    ((DirectSum.of (Graded δ (f ≫ pY)) (i + j)).comp
        (restrictDegree δ pY f (i + j))) (GradedMonoid.GMul.mul a b) =
      ((DirectSum.of (Graded δ (f ≫ pY)) i).comp (restrictDegree δ pY f i)) a *
        ((DirectSum.of (Graded δ (f ≫ pY)) j).comp (restrictDegree δ pY f j)) b := by
  change DirectSum.of (Graded δ (f ≫ pY)) (i + j)
      (restrictDegree δ pY f (i + j) (Graded.mul δ pY a b)) =
    DirectSum.of (Graded δ (f ≫ pY)) i (restrictDegree δ pY f i a) *
      DirectSum.of (Graded δ (f ≫ pY)) j (restrictDegree δ pY f j b)
  rw [DirectSum.of_mul_of]
  apply congrArg (DirectSum.of (Graded δ (f ≫ pY)) (i + j))
  exact Subtype.ext rfl

/-- The canonical contravariant `ℤ`-algebra map on operational Chow cohomology
induced by a morphism of good algebraic spaces over `B`. -/
def restrict : ring δ pY →ₐ[ℤ] ring δ (f ≫ pY) :=
  (DirectSum.toSemiring
    (fun n ↦ (DirectSum.of (Graded δ (f ≫ pY)) n).comp (restrictDegree δ pY f n))
    (restrictOne δ pY f) (restrictMul δ pY f)).toIntAlgHom

set_option maxHeartbeats 800000 in
/-- Restriction of a homogeneous class is homogeneous restriction. -/
theorem restrict_of (n : ℤ) (c : Graded δ pY n) :
    restrict δ pY f (DirectSum.of (Graded δ pY) n c) =
      DirectSum.of (Graded δ (f ≫ pY)) n (restrictDegree δ pY f n c) :=
  DirectSum.toSemiring_of _ (restrictOne δ pY f) (restrictMul δ pY f) n c

/-- The restricted class acts on a good test `h : X' ⟶ X` by the original
class on `h ≫ f : X' ⟶ Y`. -/
theorem restrict_apply (n : ℤ) (c : Graded δ pY n)
    {X' : AlgebraicSpace S} (h : X' ⟶ X)
    [QuasiSeparated (h ≫ (f ≫ pY))] [LocallyOfFiniteType (h ≫ (f ≫ pY))]
    (k : ℤ) :
    Graded.cap δ (f ≫ pY) (restrictDegree δ pY f n c) h k =
      Graded.cap δ pY c (h ≫ f) k :=
  rfl

end Restrict

set_option maxHeartbeats 800000 in
/-- Restriction along an identity morphism is the identity algebra
homomorphism. -/
theorem restrict_id {Y : AlgebraicSpace S} (pY : Y ⟶ B)
    [QuasiSeparated pY] [LocallyOfFiniteType pY]
    [QuasiSeparated (𝟙 Y ≫ pY)] [LocallyOfFiniteType (𝟙 Y ≫ pY)] :
    restrict δ pY (𝟙 Y) = AlgHom.id ℤ (ring δ pY) := by
  refine AlgHom.coe_addMonoidHom_injective (DirectSum.addHom_ext fun n c ↦ ?_)
  change restrict δ pY (𝟙 Y) (DirectSum.of (Graded δ pY) n c) =
    DirectSum.of (Graded δ pY) n c
  rw [restrict_of]
  apply congrArg (DirectSum.of (Graded δ pY) n)
  exact Subtype.ext rfl

-- Comparing the two associations of the composite unfolds the graded ring instances.
set_option maxHeartbeats 800000 in
/-- Operational Chow-cohomology restriction is contravariantly functorial under
composition. -/
theorem restrict_comp {X Y Z : AlgebraicSpace S}
    (pZ : Z ⟶ B) (g : Y ⟶ Z) (f : X ⟶ Y)
    [QuasiSeparated pZ] [LocallyOfFiniteType pZ]
    [QuasiSeparated (g ≫ pZ)] [LocallyOfFiniteType (g ≫ pZ)]
    [QuasiSeparated ((f ≫ g) ≫ pZ)] [LocallyOfFiniteType ((f ≫ g) ≫ pZ)]
    [QuasiSeparated (f ≫ (g ≫ pZ))] [LocallyOfFiniteType (f ≫ (g ≫ pZ))] :
    restrict δ pZ (f ≫ g) = (restrict δ (g ≫ pZ) f).comp (restrict δ pZ g) := by
  apply AlgHom.coe_ringHom_injective
  apply DirectSum.ringHom_ext
  intro n c
  change restrict δ pZ (f ≫ g) (DirectSum.of (Graded δ pZ) n c) =
    restrict δ (g ≫ pZ) f (restrict δ pZ g (DirectSum.of (Graded δ pZ) n c))
  rw [restrict_of, restrict_of, restrict_of]
  apply congrArg (DirectSum.of (Graded δ ((f ≫ g) ≫ pZ)) n)
  exact Subtype.ext rfl

end AlgebraicGeometry.AlgebraicSpace.OperationalChow
