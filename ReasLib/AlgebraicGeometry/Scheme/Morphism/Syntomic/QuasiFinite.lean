/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FiberEulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.TorAmplitude
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.LocalCompleteIntersection
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Basic

/-!
# Quasi-finite syntomic morphisms

This module characterizes quasi-finite syntomic morphisms using local complete
intersections, affine presentations, and the derived naive cotangent complex.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/-- For a morphism of schemes `f : Y ⟶ X`, the following are equivalent:
`f` is locally quasi-finite and syntomic; it is locally quasi-finite, flat, and
a local complete intersection; it is locally quasi-finite, flat, locally of
finite presentation, and has local-complete-intersection fibers; it admits at
every source point a localized polynomial presentation with equally many
variables and equations; it admits there a polynomial quotient presentation
with equally many variables and equations; its derived naive cotangent complex
has Tor-amplitude in `[-1, 0]` in addition to local quasi-finiteness, flatness,
and local finite presentation; or that complex is perfect of rank zero with
the same Tor-amplitude, while `f` is flat and locally of finite presentation. -/
theorem AlgebraicGeometry.quasiFiniteSyntomic_tfae
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    let L : RingedSpace.ModuleDerived Y.toRingedSpace :=
      DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)
    List.TFAE [
      LocallyQuasiFinite f ∧ Syntomic f,
      LocallyQuasiFinite f ∧ Flat f ∧
        LocallyOfType RingHom.IsLocalCompleteIntersection f,
      LocallyQuasiFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
        ∀ x : X, IsLocalCompleteIntersectionOver (X.residueField x)
          (f.fiberToSpecResidueField x),
      LocallyQuasiFinite f ∧
        ∀ y : Y, ∃ V : Y.affineOpens, y ∈ (V : Y.Opens) ∧
          ∃ U : X.affineOpens, ∃ e : V ≤ f ⁻¹ᵁ U,
            ∃ n : ℕ, ∃ h : MvPolynomial (Fin n) Γ(X, U),
              ∃ g : Fin n → MvPolynomial (Fin n) Γ(X, U),
                ∃ q : Localization.Away h →+* Γ(Y, V),
                  Function.Surjective q ∧
                    q.comp (algebraMap Γ(X, U) (Localization.Away h)) =
                      (f.appLE U V e).hom ∧
                    RingHom.ker q = Ideal.span
                      (Set.range fun i ↦
                        algebraMap (MvPolynomial (Fin n) Γ(X, U))
                          (Localization.Away h) (g i)),
      ∀ y : Y, ∃ V : Y.affineOpens, y ∈ (V : Y.Opens) ∧
        ∃ U : X.affineOpens, ∃ e : V ≤ f ⁻¹ᵁ U,
          ∃ n : ℕ,
            ∃ P : @Algebra.Presentation Γ(X, U) Γ(Y, V) (Fin n) (Fin n)
                _ _ (f.appLE U V e).hom.toAlgebra,
              @Algebra.Presentation.IsRelativeGlobalCompleteIntersection
                Γ(X, U) Γ(Y, V) _ _ (f.appLE U V e).hom.toAlgebra n n P,
      LocallyQuasiFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
        RingedSpace.HasTorAmplitudeIn L (-1) 0,
      Flat f ∧ LocallyOfFinitePresentation f ∧
        RingedSpace.ModuleDerived.IsPerfect L ∧
          Scheme.ModuleDerived.fiberEulerChar L = (fun _ ↦ (0 : ℤ)) ∧
        RingedSpace.HasTorAmplitudeIn L (-1) 0] := sorry
