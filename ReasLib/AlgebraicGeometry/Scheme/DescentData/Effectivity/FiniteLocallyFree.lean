module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Effectivity.Local
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PointsOver

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DescentData
namespace IsEffective

/-- A descent datum along a surjective finite locally free morphism is effective if its
geometric fibers have at most `d` points and every `d`-tuple in a fiber of its component
is contained in an affine open. -/
theorem ofFiniteLocallyFree {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    [IsFiniteLocallyFree f] (d : ℕ) (hd : 0 < d)
    (h_fiber : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (p : Spec (.of K) ⟶ Y),
      Finite (pullback f p : Scheme) ∧ Nat.card (pullback f p : Scheme) ≤ d)
    (D : Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f))
    (h_affine : ∀ (y : Y)
      (v : Fin d → ((D.obj PUnit.unit).hom ≫ f).pointsOver y),
      ∃ U : (D.obj PUnit.unit).left.affineOpens,
        Set.range (fun i ↦ (v i : (D.obj PUnit.unit).left)) ⊆
          ((U : (D.obj PUnit.unit).left.Opens) : Set (D.obj PUnit.unit).left)) :
    D.IsEffective := sorry

/-- A descent datum along a surjective finite locally free morphism is effective if every
finite set in a fiber of its component is contained in an affine open. -/
theorem ofFiniteLocallyFreeOfAffineOpen {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    [IsFiniteLocallyFree f]
    (D : Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f))
    (h_affine : ∀ (y : Y) (E : Set (D.obj PUnit.unit).left), E.Finite →
      E ⊆ ((D.obj PUnit.unit).hom ≫ f).pointsOver y →
      ∃ U : (D.obj PUnit.unit).left.affineOpens,
        E ⊆ ((U : (D.obj PUnit.unit).left.Opens) : Set (D.obj PUnit.unit).left)) :
    D.IsEffective := sorry

end IsEffective
end DescentData
end Scheme
end AlgebraicGeometry
