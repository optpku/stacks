module

public import Mathlib.CategoryTheory.Localization.Linear
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy.KProjective
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy.Shift
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Shift.Category

/-!
# Morphisms into K-injective differential graded modules

This leaf gives the intrinsic DG-module analogue of Mathlib's K-injective Hom API. It exposes
the localization map as a linear equivalence and records the shift comparisons needed to pass
between explicit DG-module shifts and shifts in the derived category.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule.Homotopy.KInjective

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

/-- Localization induces a bijection on morphisms into a K-injective right DG module. -/
@[stacks 09KY "K-injective localization map bijectivity"]
theorem qMap_bijective
    (N I : K R (DifferentialGradedModule.{u, v} A))
    (hI : Homotopy.kInjective A I) :
    Function.Bijective
      ((Derived.Q A).map :
        (N ⟶ I) → ((Derived.Q A).obj N ⟶ (Derived.Q A).obj I)) := sorry

/-- Morphisms into a K-injective right DG module are unchanged by passage from the intrinsic
homotopy category to the derived category. -/
@[stacks 09KY "K-injective localization Hom equivalence for DG modules"]
noncomputable def homLinearEquiv
    (N I : K R (DifferentialGradedModule.{u, v} A))
    (hI : Homotopy.kInjective A I) :
    (N ⟶ I) ≃ₗ[R] ((Derived.Q A).obj N ⟶ (Derived.Q A).obj I) :=
  LinearEquiv.ofBijective ((Derived.Q A).mapLinearMap R)
    (qMap_bijective N I hI)

/-- The K-injective Hom equivalence is the localization map on every morphism. -/
@[stacks 09KY "K-injective Hom equivalence evaluation", simp]
theorem homLinearEquiv_apply
    (N I : K R (DifferentialGradedModule.{u, v} A))
    (hI : Homotopy.kInjective A I) (f : N ⟶ I) :
    homLinearEquiv N I hI f = (Derived.Q A).map f := sorry

/-- K-injective objects are stable under every integer shift in the intrinsic DG homotopy
category. -/
@[stacks 09KY "shift stability of K-injective objects"]
theorem shift (I : K R (DifferentialGradedModule.{u, v} A))
    (hI : Homotopy.kInjective A I) (n : ℤ) :
    Homotopy.kInjective A (I⟦n⟧) := sorry

/-- The homotopy object represented by an explicit shift of a K-injective DG module is again
K-injective. -/
@[stacks 09KY "explicit shift stability of K-injective modules"]
theorem toK_shift (I : DifferentialGradedModule.{u, v} A)
    (hI : Homotopy.kInjective A ((toK A).obj I)) (n : ℤ) :
    Homotopy.kInjective A ((toK A).obj I[n]) := sorry

end DifferentialGradedModule.Homotopy.KInjective

namespace DifferentialGradedModule.Derived

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

/-- A quasi-isomorphism in the intrinsic DG homotopy category determines a specified
isomorphism after localization. -/
@[stacks 09KY "localized isomorphism from a quasi-isomorphism"]
noncomputable def isoOfQuasiIso
    {M N : K R (DifferentialGradedModule.{u, v} A)} (f : M ⟶ N)
    (hf : quasiIso A f) : (Q A).obj M ≅ (Q A).obj N :=
  Localization.isoOfHom (Q A) (quasiIso A) f hf

/-- The forward morphism of `isoOfQuasiIso f hf` is the localized morphism `Q.map f`. -/
@[stacks 09KY "localized quasi-isomorphism evaluation", simp]
theorem isoOfQuasiIso_hom
    {M N : K R (DifferentialGradedModule.{u, v} A)} (f : M ⟶ N)
    (hf : quasiIso A f) :
    (isoOfQuasiIso f hf).hom = (Q A).map f := sorry

/-- The derived image of an explicit shifted DG module agrees with the categorical shift of
its derived image. -/
@[stacks 09KY "derived image and explicit shift comparison"]
noncomputable def toKShiftIso (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (Q A).obj ((toK A).obj M[n]) ≅ ((Q A).obj ((toK A).obj M))⟦n⟧ :=
  (Q A).mapIso (((toK A).commShiftIso n).app M) ≪≫
    ((Q A).commShiftIso n).app ((toK A).obj M)

/-- The forward map of the derived shift comparison is the composite of the two canonical
commutation-with-shift maps. -/
@[stacks 09KY "derived shift comparison evaluation"]
theorem toKShiftIso_hom (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (toKShiftIso M n).hom =
      (Q A).map (((toK A).commShiftIso n).hom.app M) ≫
        ((Q A).commShiftIso n).hom.app ((toK A).obj M) := sorry

/-- The canonical linear map from enriched Hom-complex cohomology to shifted morphisms in the
derived category of right DG modules. -/
@[stacks 0CS6 "DG Hom cohomology to derived Ext"]
noncomputable def homologyHomLinearMap
    (M N : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (DifferentialGradedCategory.homComplex M N).homology n →ₗ[R]
      ShiftedHom ((Q A).obj ((toK A).obj M)) ((Q A).obj ((toK A).obj N)) n where
  toFun x :=
    (Q A).map (Homotopy.homotopyOfHomology M N n x) ≫
      (toKShiftIso N n).hom
  map_add' := sorry
  map_smul' := sorry

/-- Evaluation of `homologyHomLinearMap` localizes the homotopy class represented by the
cohomology class and then applies the canonical shift comparison. -/
@[stacks 0CS6 "DG Hom cohomology comparison evaluation", simp]
theorem homologyHomLinearMap_apply
    (M N : DifferentialGradedModule.{u, v} A) (n : ℤ)
    (x : (DifferentialGradedCategory.homComplex M N).homology n) :
    homologyHomLinearMap M N n x =
      (Q A).map (Homotopy.homotopyOfHomology M N n x) ≫
        (toKShiftIso N n).hom := sorry

/-- Hom-complex cohomology computes shifted derived Hom when the source DG module is
K-projective. -/
@[stacks 0CS6 "DG Hom cohomology comparison bijectivity"]
theorem homologyHomLinearMap_bijective
    (M N : DifferentialGradedModule.{u, v} A) (n : ℤ)
    (hM : Homotopy.kProjective A ((toK A).obj M)) :
    Function.Bijective (homologyHomLinearMap M N n) := sorry

/-- The linear equivalence from Hom-complex cohomology to shifted derived Hom for a
K-projective source DG module. -/
@[stacks 0CS6 "DG Hom cohomology comparison equivalence"]
noncomputable def homologyHomLinearEquiv
    (M N : DifferentialGradedModule.{u, v} A) (n : ℤ)
    (hM : Homotopy.kProjective A ((toK A).obj M)) :
    (DifferentialGradedCategory.homComplex M N).homology n ≃ₗ[R]
      ShiftedHom ((Q A).obj ((toK A).obj M)) ((Q A).obj ((toK A).obj N)) n :=
  LinearEquiv.ofBijective (homologyHomLinearMap M N n)
    (homologyHomLinearMap_bijective M N n hM)

/-- The forward map of `homologyHomLinearEquiv` is the canonical cohomology-to-derived-Hom
linear map. -/
@[stacks 0CS6 "DG Hom cohomology comparison equivalence evaluation", simp]
theorem homologyHomLinearEquiv_apply
    (M N : DifferentialGradedModule.{u, v} A) (n : ℤ)
    (hM : Homotopy.kProjective A ((toK A).obj M))
    (x : (DifferentialGradedCategory.homComplex M N).homology n) :
    homologyHomLinearEquiv M N n hM x = homologyHomLinearMap M N n x := sorry

end DifferentialGradedModule.Derived
