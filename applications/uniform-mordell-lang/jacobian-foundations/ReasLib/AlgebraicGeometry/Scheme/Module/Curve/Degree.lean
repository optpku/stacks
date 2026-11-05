module

public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Degrees of vector bundles on proper curves

The degree of a finite locally free module on a proper curve is its Euler characteristic relative
to the structure sheaf, normalized by the rank.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

section

variable {k : Type u} [Field k]
variable {X : Scheme.{u}}

/-- The degree of a finite locally free module of rank `n` on a proper scheme of dimension at most
one is `χ(X, ℰ) - n χ(X, 𝒪_X)`. -/
@[stacks 0AYR]
def curveDegree (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (_ : topologicalKrullDim X ≤ 1) (ℰ : X.Modules) (n : ℕ)
    [IsFiniteLocallyFreeOfRank n ℰ] : ℤ :=
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : ℰ.IsCoherent := isCoherent_of_isFiniteLocallyFreeOfRank n ℰ
  Scheme.Hom.eulerCharacteristic f ℰ -
    (n : ℤ) * Scheme.Hom.eulerCharacteristic f
      (SheafOfModules.unit X.ringCatSheaf : X.Modules)

/-- The defining normal form for `curveDegree`. -/
@[stacks 0AYR]
theorem curveDegree_def (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (ℰ : X.Modules) (n : ℕ)
    [IsFiniteLocallyFreeOfRank n ℰ] :
    let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    let _ : ℰ.IsCoherent := isCoherent_of_isFiniteLocallyFreeOfRank n ℰ
    curveDegree f hdim ℰ n =
      Scheme.Hom.eulerCharacteristic f ℰ -
        (n : ℤ) * Scheme.Hom.eulerCharacteristic f
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) := rfl

/-- For an invertible module on a proper scheme of dimension at most one, the degree is its Euler
characteristic relative to the structure sheaf. -/
@[stacks 0AYR]
theorem curveDegree_eq_eulerCharacteristic_sub_structureSheaf_of_invertible
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (ℒ : X.Modules) [Invertible ℒ] :
    let _ : IsFiniteLocallyFreeOfRank 1 ℒ :=
      isFiniteLocallyFreeOfRankOne_of_invertible ℒ
    let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    let _ : ℒ.IsCoherent := isCoherent_of_isFiniteLocallyFreeOfRank 1 ℒ
    curveDegree f hdim ℒ 1 =
      Scheme.Hom.eulerCharacteristic f ℒ -
        Scheme.Hom.eulerCharacteristic f
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) := by
  simp only [curveDegree, Nat.cast_one, one_mul]

/-- The degree of an invertible module on a proper scheme of dimension at most one, using its
canonical rank-one finite locally free structure. -/
noncomputable def curveDegreeOfInvertible
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (ℒ : X.Modules) [Invertible ℒ] : ℤ :=
  let _ : IsFiniteLocallyFreeOfRank 1 ℒ :=
    isFiniteLocallyFreeOfRankOne_of_invertible ℒ
  curveDegree f hdim ℒ 1

/-- The degree of an invertible module is its Euler characteristic relative to the structure
sheaf. -/
theorem curveDegreeOfInvertible_eq_eulerCharacteristic_sub_structureSheaf
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (ℒ : X.Modules) [Invertible ℒ] :
    curveDegreeOfInvertible f hdim ℒ =
      Scheme.Hom.eulerCharacteristic f ℒ -
        Scheme.Hom.eulerCharacteristic f
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) := by
  simp only [curveDegreeOfInvertible, curveDegree, Nat.cast_one, one_mul]

/-- Curve degree is additive along a short exact complex of finite locally free modules of
constant rank on a proper scheme over a field of topological Krull dimension at most one. -/
@[stacks 0AYS]
theorem curveDegree_eq_add_of_shortExact_of_properOverField
    {S : ShortComplex X.Modules} {n₁ n₂ n₃ : ℕ}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    [IsFiniteLocallyFreeOfRank n₁ S.X₁]
    [IsFiniteLocallyFreeOfRank n₂ S.X₂]
    [IsFiniteLocallyFreeOfRank n₃ S.X₃]
    (hS : S.ShortExact) :
    curveDegree f hdim S.X₂ n₂ =
      curveDegree f hdim S.X₁ n₁ + curveDegree f hdim S.X₃ n₃ := sorry

/-- Degree is independent of the representative of a finite locally free sheaf.
The comparison is induced by the given sheaf isomorphism. -/
theorem curveDegree_eq_of_iso
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) {E F : X.Modules} (n : ℕ)
    [IsFiniteLocallyFreeOfRank n E] [IsFiniteLocallyFreeOfRank n F] (e : E ≅ F) :
    curveDegree f hdim E n = curveDegree f hdim F n := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : E.IsCoherent := isCoherent_of_isFiniteLocallyFreeOfRank n E
  letI : F.IsCoherent := isCoherent_of_isFiniteLocallyFreeOfRank n F
  exact congrArg (fun χ => χ - (n : ℤ) * Scheme.Hom.eulerCharacteristic f
    (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (Scheme.Hom.eulerCharacteristic_eq_of_iso f e)

/-- The invertible-sheaf degree descends through actual coefficient-sheaf isomorphisms.
This is the interface needed by a Picard quotient; it does not prove tensor additivity. -/
theorem curveDegreeOfInvertible_eq_of_iso
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) {L M : X.Modules}
    [Invertible L] [Invertible M] (e : L ≅ M) :
    curveDegreeOfInvertible f hdim L = curveDegreeOfInvertible f hdim M := by
  letI := isFiniteLocallyFreeOfRankOne_of_invertible L
  letI := isFiniteLocallyFreeOfRankOne_of_invertible M
  exact curveDegree_eq_of_iso f hdim 1 e

namespace Invertible

/-- An explicit invertibility witness gives the canonical degree of its module on a proper
scheme of dimension at most one. -/
noncomputable def curveDegree {ℒ : X.Modules} (hℒ : Invertible ℒ)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) : ℤ :=
  @curveDegreeOfInvertible k _ X f _ hdim ℒ hℒ

/-- The degree computed from an explicit invertibility witness agrees with the canonical
degree of the invertible module. -/
theorem curveDegree_eq (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (ℒ : X.Modules) [hℒ : Invertible ℒ] :
    hℒ.curveDegree f hdim = curveDegreeOfInvertible f hdim ℒ := rfl

end Invertible

end

end AlgebraicGeometry.Scheme.Modules
