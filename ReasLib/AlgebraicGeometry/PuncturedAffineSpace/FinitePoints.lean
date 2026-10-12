/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace.AffinePlane
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AffineCover

/-!
# Finite closed points of the affine plane

This module records the closed `k`-points of `affinePlane k` associated to tuples
`Fin 2 → k`, together with the open complement of a finite family of such points.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedAffinePlane

variable {k : Type u}

/-- The global section of `Spec k` associated to an element of `k`. -/
def specSection [CommRing k] (a : k) : Γ(Spec (CommRingCat.of k), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv a

/-- The morphism `Spec k ⟶ affinePlane k` determined by the coordinates `p`. -/
def pointHom [CommRing k] (p : Fin 2 → k) :
    Spec (CommRingCat.of k) ⟶ affinePlane k :=
  AffineSpace.homOfVector (𝟙 _) (fun i ↦ specSection (p i.down.down))

/-- A rational point of the affine plane lies over `Spec k`. -/
theorem pointHom_toBase [CommRing k] (p : Fin 2 → k) :
    pointHom p ≫ toBase k = 𝟙 _ := sorry

/-- A rational point of the affine plane is a closed immersion. -/
instance instIsClosedImmersionPointHom [Field k] (p : Fin 2 → k) :
    IsClosedImmersion (pointHom p) := sorry

/-- The closed point of `affinePlane k` with coordinates `p`. -/
def closedPoint [Field k] (p : Fin 2 → k) : affinePlane k :=
  pointHom p (IsLocalRing.closedPoint k)

/-- `closedPoint p` is the image of the closed point of `Spec k` under `pointHom p`. -/
theorem closedPoint_spec [Field k] (p : Fin 2 → k) :
    closedPoint p = pointHom p (IsLocalRing.closedPoint k) := sorry

/-- The image of a rational point of the affine plane is a closed point. -/
theorem closedPoint_mem_closedPoints [Field k] (p : Fin 2 → k) :
    closedPoint p ∈ closedPoints (affinePlane k) := sorry

/-- The origin of the affine plane is the closed point with both coordinates zero. -/
theorem closedPoint_zero (k : Type u) [Field k] :
    closedPoint (0 : Fin 2 → k) = origin k := sorry

variable {ι : Type u}

/-- The image of a finite family of rational points of the affine plane is closed. -/
theorem isClosed_range_closedPoint [Finite ι] [Field k] (p : ι → Fin 2 → k) :
    IsClosed (Set.range (fun i ↦ closedPoint (p i))) := sorry

/-- The open complement in `affinePlane k` of a finite family of closed `k`-points. -/
def complementOpen [Finite ι] [Field k] (p : ι → Fin 2 → k) :
    (affinePlane k).Opens :=
  ⟨(Set.range (fun i ↦ closedPoint (p i)))ᶜ, (isClosed_range_closedPoint p).isOpen_compl⟩

/-- The carrier of `complementOpen p` is the set-theoretic complement of the given closed
points. -/
theorem coe_complementOpen [Finite ι] [Field k] (p : ι → Fin 2 → k) :
    (complementOpen p : Set (affinePlane k)) =
      (Set.range (fun i ↦ closedPoint (p i)))ᶜ := sorry

/-- A point of the affine plane lies in `complementOpen p` if and only if it is not one of
the given closed `k`-points. -/
theorem mem_complementOpen_iff [Finite ι] [Field k] (p : ι → Fin 2 → k)
    {x : affinePlane k} :
    x ∈ complementOpen p ↔ x ∉ Set.range (fun i ↦ closedPoint (p i)) := sorry

/-- The complement of finitely many closed `k`-points in the affine plane is a union of two
affine opens. -/
theorem exists_isAffineOpen_sup_eq_complementOpen [Finite ι] [Field k]
    (p : ι → Fin 2 → k) :
    ∃ U V : (affinePlane k).Opens,
      IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = complementOpen p := sorry

/-- The open subscheme `complementOpen p` admits an affine open cover indexed by `Fin 2`. -/
theorem complementOpen_hasCard_two [Finite ι] [Field k] (p : ι → Fin 2 → k) :
    Scheme.AffineOpenCover.HasCard (complementOpen p).toScheme 2 := sorry

end AlgebraicGeometry.PuncturedAffinePlane

end
