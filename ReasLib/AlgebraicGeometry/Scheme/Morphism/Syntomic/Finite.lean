/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.QuasiFinite

/-!
# Finite syntomic morphisms

This module characterizes finite syntomic morphisms through local complete
intersections, affine presentations, and the derived naive cotangent complex.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/-- For a morphism of schemes `f : Y ⟶ X`, the following six conditions are equivalent:
`f` is finite and syntomic; it is finite, flat, and a local complete intersection;
it is finite, flat, locally of finite presentation, and has local-complete-intersection
fibers; locally on the target it is the spectrum of a polynomial quotient by as many
equations as variables; its derived naive cotangent complex has Tor-amplitude in
`[-1, 0]` in addition to finiteness, flatness, and local finite presentation; or that
complex is perfect of fiber Euler characteristic zero with the same Tor-amplitude and
the same three properties of `f`. -/
theorem AlgebraicGeometry.finiteSyntomic_tfae
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    let L : RingedSpace.ModuleDerived Y.toRingedSpace :=
      DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)
    List.TFAE [
      IsFinite f ∧ Syntomic f,
      IsFinite f ∧ Flat f ∧
        LocallyOfType RingHom.IsLocalCompleteIntersection f,
      IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
        ∀ x : X, IsLocalCompleteIntersectionOver (X.residueField x)
          (f.fiberToSpecResidueField x),
      IsFinite f ∧
        ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
          ∃ n : ℕ, ∃ g : Fin n → MvPolynomial (Fin n) Γ(X, U),
            ∃ q : MvPolynomial (Fin n) Γ(X, U) →+* Γ(Y, f ⁻¹ᵁ U),
              Function.Surjective q ∧
                q.comp (MvPolynomial.C : Γ(X, U) →+* MvPolynomial (Fin n) Γ(X, U)) =
                  (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom ∧
                RingHom.ker q = Ideal.span (Set.range g),
      IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
        RingedSpace.HasTorAmplitudeIn L (-1) 0,
      IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
        RingedSpace.ModuleDerived.IsPerfect L ∧
          Scheme.ModuleDerived.fiberEulerChar L = (fun _ ↦ (0 : ℤ)) ∧
        RingedSpace.HasTorAmplitudeIn L (-1) 0] := sorry
