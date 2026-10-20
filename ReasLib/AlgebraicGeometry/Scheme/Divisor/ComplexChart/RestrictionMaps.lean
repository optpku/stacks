module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.GlobalCover

/-!
# Actual coordinate restriction maps for the global graph family

The coefficient homomorphism is the structure-sheaf restriction. The Rees map
is its coefficientwise lift, not an arbitrary homomorphism or an existence
witness. The center-containment condition is a property of these fixed ideals;
comparing products from different perfect models remains separate work.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PerfectGraphAtlas

variable {X Y : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace)
  (hE : RingedSpace.ModuleDerived.IsPerfect E) (p : Y ⟶ X) (D : Y.IdealSheafData)

/-- The actual coefficient restriction between two nested coordinate opens. -/
def coefficientRestriction (i j : divisorChartIndex E hE p D)
    (h : (j.1.U : Y.Opens) ≤ i.1.U) : Γ(Y, i.1.U) →+* Γ(Y, j.1.U) :=
  (Y.presheaf.map (homOfLE h).op).hom

/-- Restricting coefficients to the same open is the identity. -/
theorem coefficientRestriction_id (i : divisorChartIndex E hE p D) :
    coefficientRestriction E hE p D i i le_rfl = RingHom.id _ := by
  change (Y.presheaf.map (𝟙 (Opposite.op (i.1.U : Y.Opens)))).hom = _
  exact congrArg CommRingCat.Hom.hom (Y.presheaf.map_id _)

/-- The coordinate restriction maps compose exactly as the sheaf restriction functor. -/
theorem coefficientRestriction_comp (i j k : divisorChartIndex E hE p D)
    (hij : (j.1.U : Y.Opens) ≤ i.1.U) (hjk : (k.1.U : Y.Opens) ≤ j.1.U) :
    (coefficientRestriction E hE p D j k hjk).comp
        (coefficientRestriction E hE p D i j hij) =
      coefficientRestriction E hE p D i k (hjk.trans hij) := by
  exact congrArg CommRingCat.Hom.hom
    (Y.presheaf.map_comp (homOfLE hij).op (homOfLE hjk).op).symm

/-- The Rees-algebra restriction induced by the actual coordinate map. -/
def reesRestriction (i j : divisorChartIndex E hE p D)
    (h : (j.1.U : Y.Opens) ≤ i.1.U)
    (hcenter : i.1.productIdeal ≤
      Ideal.comap (coefficientRestriction E hE p D i j h) j.1.productIdeal) :
    reesAlgebra i.1.productIdeal →+* reesAlgebra j.1.productIdeal :=
  i.1.graphReesMap j.1 (coefficientRestriction E hE p D i j h) hcenter

/-- Each coefficient of the Rees transition is the structure-sheaf restriction of the input coefficient. -/
theorem reesRestriction_coeff (i j : divisorChartIndex E hE p D)
    (h : (j.1.U : Y.Opens) ≤ i.1.U)
    (hcenter : i.1.productIdeal ≤
      Ideal.comap (coefficientRestriction E hE p D i j h) j.1.productIdeal)
    (x : reesAlgebra i.1.productIdeal) (n : ℕ) :
    ((reesRestriction E hE p D i j h hcenter x).1).coeff n =
      coefficientRestriction E hE p D i j h (x.1.coeff n) :=
  i.1.graphReesMap_coeff j.1 _ hcenter x n

/-- The map on a distinguished generator is specified by its restricted coefficient. -/
theorem reesRestriction_generator (i j : divisorChartIndex E hE p D)
    (h : (j.1.U : Y.Opens) ≤ i.1.U)
    (hcenter : i.1.productIdeal ≤
      Ideal.comap (coefficientRestriction E hE p D i j h) j.1.productIdeal)
    (x : i.1.productIdeal) :
    reesRestriction E hE p D i j h hcenter (i.1.graphGenerator x) =
      j.1.graphGenerator ⟨coefficientRestriction E hE p D i j h x.1, hcenter x.2⟩ :=
  i.1.graphReesMap_generator j.1 _ hcenter x

/-- Center containment for a composite follows from the two fixed containment proofs. -/
theorem centerRestriction_comp (i j k : divisorChartIndex E hE p D)
    (hij : (j.1.U : Y.Opens) ≤ i.1.U) (hjk : (k.1.U : Y.Opens) ≤ j.1.U)
    (hcij : i.1.productIdeal ≤ Ideal.comap (coefficientRestriction E hE p D i j hij) j.1.productIdeal)
    (hcjk : j.1.productIdeal ≤ Ideal.comap (coefficientRestriction E hE p D j k hjk) k.1.productIdeal) :
    i.1.productIdeal ≤ Ideal.comap (coefficientRestriction E hE p D i k (hjk.trans hij)) k.1.productIdeal := by
  intro x hx
  change coefficientRestriction E hE p D i k (hjk.trans hij) x ∈ k.1.productIdeal
  rw [← coefficientRestriction_comp E hE p D i j k hij hjk]
  exact hcjk (hcij hx)

/-- The explicit Rees restrictions satisfy the cocycle equation on a chain of coordinate refinements. -/
theorem reesRestriction_comp (i j k : divisorChartIndex E hE p D)
    (hij : (j.1.U : Y.Opens) ≤ i.1.U) (hjk : (k.1.U : Y.Opens) ≤ j.1.U)
    (hcij : i.1.productIdeal ≤ Ideal.comap (coefficientRestriction E hE p D i j hij) j.1.productIdeal)
    (hcjk : j.1.productIdeal ≤ Ideal.comap (coefficientRestriction E hE p D j k hjk) k.1.productIdeal) :
    (reesRestriction E hE p D j k hjk hcjk).comp (reesRestriction E hE p D i j hij hcij) =
      reesRestriction E hE p D i k (hjk.trans hij)
        (centerRestriction_comp E hE p D i j k hij hjk hcij hcjk) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  change ((reesRestriction E hE p D j k hjk hcjk
    (reesRestriction E hE p D i j hij hcij x)).1).coeff n = _
  rw [reesRestriction_coeff, reesRestriction_coeff, reesRestriction_coeff]
  exact congrArg (fun f => f (x.1.coeff n))
    (coefficientRestriction_comp E hE p D i j k hij hjk)

end AlgebraicGeometry.Scheme.PerfectGraphAtlas
