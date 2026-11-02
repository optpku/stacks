/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Module
public import ReasLib.RingTheory.Depth
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.FiniteLength
public import ReasLib.Algebra.Homology.DerivedCategory.InjectiveAmplitude.Ext
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.RHom

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped DerivedExt ENat

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

/-- Cohomology of canonical derived `RHom` from a finite module into a normalized dualizing
complex is finite in every degree. -/
theorem extModuleFinite
    (A M : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
    (comparison :
      CategoryTheory.DerivedCategory.InternalHom.RHom.ClosedComparison (A := A))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : ω.IsNormalizedDualizingComplex comparison.closed) (i : ℤ) :
    Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-i)).obj
        ((MonoidalClosed.ihomOf comparison.closed
          (ModuleCat.single0 (ModuleCat.of A M))).obj ω)) := sorry

/-- Nonzero degree-`i` cohomology of derived internal Hom into a normalized dualizing
complex occurs between the negative support dimension and degree zero. -/
theorem extDegreeBounds
    (A M : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (C : CanonicalClosedPresentation (A := A))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : ω.IsCanonicalNormalizedDualizingComplex C)
    (i : ℤ)
    (hi : ¬ IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((InternalHom.RHom.obj (A := A)
          (ModuleCat.single0 (ModuleCat.of A M)) ω)))) :
    ∃ d : ℕ, Module.supportDim A M = .some (d : ℕ∞) ∧ -(d : ℤ) ≤ i ∧ i ≤ 0 := sorry

/-- The support dimension of degree-`i` cohomology of derived internal Hom into a
normalized dualizing complex is either bottom, for zero cohomology, or at most `-i`. -/
theorem supportDim_ext_le
    (A M : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (C : CanonicalClosedPresentation (A := A))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : ω.IsCanonicalNormalizedDualizingComplex C)
    (i : ℤ) :
    Module.supportDim A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          ((InternalHom.RHom.obj (A := A)
            (ModuleCat.single0 (ModuleCat.of A M)) ω))) = ⊥ ∨
      ∃ e : ℕ, Module.supportDim A
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
            ((InternalHom.RHom.obj (A := A)
              (ModuleCat.single0 (ModuleCat.of A M)) ω))) =
        .some (e : ℕ∞) ∧ (e : ℤ) ≤ -i := sorry

/-- The depth of a finite module over a Noetherian local ring is the infimum of the
nonnegative degrees whose oppositely indexed derived internal-Hom cohomology is nonzero. -/
theorem depth_eq_sInf_nonzero_extDegrees
    (A M : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H) :
    moduleDepth A M =
      sInf {d : ℕ∞ | ∃ δ : ℕ, d = (δ : ℕ∞) ∧
        ¬ IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(δ : ℤ))).obj
            ((MonoidalClosed.ihomOf H (ModuleCat.single0 (ModuleCat.of A M))).obj ω))} := sorry

/-- A normalized dualizing complex over a Noetherian local ring of Krull dimension `d`
has injective amplitude in `[-d, 0]`. -/
theorem hasInjectiveAmplitudeIn
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (C : CanonicalClosedPresentation (A := A))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : ω.IsCanonicalNormalizedDualizingComplex C)
    (d : ℕ) (hd : ringKrullDim A = d) :
    ω.HasInjectiveAmplitudeIn (-(d : ℤ)) 0 := sorry

/-- Derived Ext from any module into a normalized dualizing complex vanishes outside
the interval determined by the Krull dimension of the ring. -/
theorem ext_subsingleton
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (C : CanonicalClosedPresentation (A := A))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : ω.IsCanonicalNormalizedDualizingComplex C)
    (d : ℕ) (hd : ringKrullDim A = d) (M : ModuleCat.{u} A) (i : ℤ)
    (hi : i ∉ Set.Icc (-(d : ℤ)) 0) :
    Subsingleton (Ext⁽i⁾(ModuleCat.single0 M, ω)) := sorry

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex
