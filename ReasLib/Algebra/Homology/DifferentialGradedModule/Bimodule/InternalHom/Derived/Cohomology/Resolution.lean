/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Derived.Cohomology
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Derived.Cohomology.Representability
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Derived.Resolution.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of resolution models for derived internal Hom

This leaf relates the explicit cohomology computed from a property-(I) resolution to the
resolution-independent cohomology of the abstract derived internal-Hom functor.  It also records
that this route agrees with the direct K-injective shifted-Hom comparison.

The resolution-facing declarations below intentionally use the SameCarrier `PropertyI` boundary
`B : CochainDGAlgebra.{u,v}` and `T : DifferentialGradedBimodule.{u,v,w,v}`.  Mixed-carrier
downstream arguments should use `Cohomology.linearEquiv`, `uliftIso`, or `uliftBifunctorIso`
from the resolution-independent leaf.  A mixed resolution API belongs with a derived-compatible
`ULift`/`PropertyI` bridge, not with an ad hoc cast in this file.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedBimodule.InternalHom.Derived.Cohomology

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, v} R}

/-- Applying derived homology to the property-(I) resolution model identifies strict
internal-Hom cohomology with the cohomology of abstract derived internal Hom. -/
@[stacks 0CS5 "cohomology of the property-I derived internal-Hom model"]
noncomputable def Resolution.iso (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ) :
    (DifferentialGradedBimodule.internalHom T I.obj).homology n ≅
      (DifferentialGradedModule.Derived.homologyFunctor A n).obj
        ((InternalHom.derivedFunctor T).obj
          ((DifferentialGradedModule.Derived.Q B).obj
            ((DifferentialGradedModule.toK B).obj M))) :=
  (DifferentialGradedModule.Homotopy.homologyIso A
      (DifferentialGradedBimodule.internalHom T I.obj) n).symm ≪≫
    (DifferentialGradedModule.Derived.homologyFunctorFactors A n).symm.app
      ((DifferentialGradedModule.toK A).obj
        (DifferentialGradedBimodule.internalHom T I.obj)) ≪≫
    (DifferentialGradedModule.Derived.homologyFunctor A n).mapIso
      (InternalHom.Derived.Resolution.modelIso T I)

/-- The forward cohomology-model comparison first inserts the localization factorization and
then applies derived homology to the resolution-model isomorphism. -/
@[simp, stacks 0CS5 "forward property-I cohomology model comparison"]
theorem Resolution.iso_hom (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ) :
    (Resolution.iso T I n).hom =
      (DifferentialGradedModule.Homotopy.homologyIso A
          (DifferentialGradedBimodule.internalHom T I.obj) n).inv ≫
        (DifferentialGradedModule.Derived.homologyFunctorFactors A n).inv.app
          ((DifferentialGradedModule.toK A).obj
            (DifferentialGradedBimodule.internalHom T I.obj)) ≫
        (DifferentialGradedModule.Derived.homologyFunctor A n).map
          (InternalHom.Derived.Resolution.modelIso T I).hom := sorry

/-- The inverse cohomology-model comparison first applies derived homology to the inverse
resolution-model isomorphism and then removes the localization factorization. -/
@[simp, stacks 0CS5 "inverse property-I cohomology model comparison"]
theorem Resolution.iso_inv (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ) :
    (Resolution.iso T I n).inv =
      (DifferentialGradedModule.Derived.homologyFunctor A n).map
          (InternalHom.Derived.Resolution.modelIso T I).inv ≫
        (DifferentialGradedModule.Derived.homologyFunctorFactors A n).hom.app
          ((DifferentialGradedModule.toK A).obj
            (DifferentialGradedBimodule.internalHom T I.obj)) ≫
        (DifferentialGradedModule.Homotopy.homologyIso A
          (DifferentialGradedBimodule.internalHom T I.obj) n).hom := sorry

section Representability

variable {A B : CochainDGAlgebra.{u, v} R}

/-- The resolution-independent comparison, specialized through a property-(I) model. -/
@[stacks 0CS5 "property-I model of the derived internal-Hom cohomology comparison"]
noncomputable def Resolution.linearEquiv
    (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ) :
    (DifferentialGradedBimodule.internalHom T I.obj).homology n ≃ₗ[R]
      ((DifferentialGradedModule.Derived.Q B).obj
          ((DifferentialGradedModule.toK B).obj T.toRightModule) ⟶
        ((DifferentialGradedModule.Derived.Q B).obj
          ((DifferentialGradedModule.toK B).obj M))⟦n⟧) :=
  (Resolution.iso.{u, v, v} T I n).toLinearEquiv.trans
    (DifferentialGradedBimodule.InternalHom.Derived.Cohomology.linearEquiv T
      ((DifferentialGradedModule.Derived.Q B).obj
        ((DifferentialGradedModule.toK B).obj M)) n)

/-- Evaluating the resolution-independent model comparison means transporting a strict
cohomology class to derived cohomology and applying the canonical representability equivalence. -/
@[simp, stacks 0CS5 "formula for property-I cohomology representability"]
theorem Resolution.linearEquiv_apply
    (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ)
    (x : (DifferentialGradedBimodule.internalHom T I.obj).homology n) :
    Resolution.linearEquiv T I n x =
      DifferentialGradedBimodule.InternalHom.Derived.Cohomology.linearEquiv T
        ((DifferentialGradedModule.Derived.Q B).obj
          ((DifferentialGradedModule.toK B).obj M)) n
        (ModuleCat.Hom.hom (Resolution.iso.{u, v, v} T I n).hom x) := sorry

/-- The inverse comparison first uses representability and then transports the resulting
derived cohomology class back to the strict property-(I) model. -/
@[simp, stacks 0CS5 "inverse formula for property-I cohomology representability"]
theorem Resolution.linearEquiv_symm_apply
    (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ)
    (f : (DifferentialGradedModule.Derived.Q B).obj
        ((DifferentialGradedModule.toK B).obj T.toRightModule) ⟶
      ((DifferentialGradedModule.Derived.Q B).obj
        ((DifferentialGradedModule.toK B).obj M))⟦n⟧) :
    (Resolution.linearEquiv T I n).symm f =
      ModuleCat.Hom.hom (Resolution.iso.{u, v, v} T I n).inv
        ((DifferentialGradedBimodule.InternalHom.Derived.Cohomology.linearEquiv T
          ((DifferentialGradedModule.Derived.Q B).obj
            ((DifferentialGradedModule.toK B).obj M)) n).symm f) := sorry

/-- The abstract-derived and direct K-injective constructions of the resolution comparison
agree. -/
@[stacks 0CS5 "compatibility of the two property-I cohomology comparisons"]
theorem Resolution.linearEquiv_eq_direct
    (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ) :
    Resolution.linearEquiv T I n =
      InternalHom.Cohomology.resolutionLinearEquiv.{u, v, v} T I n := sorry

end Representability

namespace Resolution

/-- The cohomology comparison is contravariantly natural in the bimodule source. -/
@[reassoc, stacks 0CS5 "source naturality of property-I resolution cohomology"]
theorem iso_hom_naturality_source
    {T T' : DifferentialGradedBimodule.{u, v, w, v} A B} (f : T ⟶ T')
    {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ) :
    InternalHom.Cohomology.sourceMap f I.obj n ≫
        (iso T I n).hom =
      (iso T' I n).hom ≫
        (DifferentialGradedModule.Derived.homologyFunctor A n).map
          ((InternalHom.derivedNatTrans f).app
            ((DifferentialGradedModule.Derived.Q B).obj
              ((DifferentialGradedModule.toK B).obj M))) := sorry

/-- The cohomology comparison is covariantly natural in compatible maps of property-(I)
resolutions. -/
@[reassoc, stacks 0CS5 "target naturality of property-I resolution cohomology"]
theorem iso_hom_naturality_target
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M N : DifferentialGradedModule.{u, v} B} {f : M ⟶ N}
    {I : DifferentialGradedModule.PropertyI.Resolution B M}
    {J : DifferentialGradedModule.PropertyI.Resolution B N}
    (m : DifferentialGradedModule.PropertyI.Resolution.Map f I J) (n : ℤ) :
    InternalHom.Cohomology.targetMap T m.hom n ≫
        (iso T J n).hom =
      (iso T I n).hom ≫
        (DifferentialGradedModule.Derived.homologyFunctor A n).map
          ((InternalHom.derivedFunctor T).map
            ((DifferentialGradedModule.Derived.Q B).map
              ((DifferentialGradedModule.toK B).map f))) := sorry

section Representability

variable {A B : CochainDGAlgebra.{u, v} R}

/-- The resolution-independent linear comparison is contravariantly natural in the bimodule
source. -/
@[stacks 0CS5 "source naturality of the property-I cohomology equivalence"]
theorem linearEquiv_naturality_source
    {T T' : DifferentialGradedBimodule.{u, v, v, v} A B} (f : T ⟶ T')
    {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ)
    (x : (DifferentialGradedBimodule.internalHom T' I.obj).homology n) :
    linearEquiv T I n
        (InternalHom.Cohomology.sourceMap f I.obj n x) =
      (DifferentialGradedModule.Derived.Q B).map
          ((DifferentialGradedModule.toK B).map
            (DifferentialGradedBimodule.Hom.toRightHom f)) ≫
        linearEquiv T' I n x := sorry

/-- The resolution-independent linear comparison is covariantly natural in compatible maps
of property-(I) resolutions. -/
@[stacks 0CS5 "target naturality of the property-I cohomology equivalence"]
theorem linearEquiv_naturality_target
    (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    {M N : DifferentialGradedModule.{u, v} B} {f : M ⟶ N}
    {I : DifferentialGradedModule.PropertyI.Resolution B M}
    {J : DifferentialGradedModule.PropertyI.Resolution B N}
    (m : DifferentialGradedModule.PropertyI.Resolution.Map f I J) (n : ℤ)
    (x : (DifferentialGradedBimodule.internalHom T I.obj).homology n) :
    linearEquiv T J n
        (InternalHom.Cohomology.targetMap T m.hom n x) =
      linearEquiv T I n x ≫
        ((DifferentialGradedModule.Derived.Q B).map
          ((DifferentialGradedModule.toK B).map f))⟦n⟧' := sorry

/-- The canonical cohomology comparison between two property-(I) resolutions of the same
target. -/
@[stacks 0CS5 "change of property-I resolution on internal-Hom cohomology"]
noncomputable def comparisonIso (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I J : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ) :
    (DifferentialGradedBimodule.internalHom T I.obj).homology n ≅
      (DifferentialGradedBimodule.internalHom T J.obj).homology n :=
  iso.{u, v, v} T I n ≪≫ (iso.{u, v, v} T J n).symm

/-- The forward cohomological change-of-resolution map factors through abstract derived
internal-Hom cohomology. -/
@[simp, stacks 0CS5 "forward change-of-resolution cohomology comparison"]
theorem comparisonIso_hom (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I J : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ) :
    (comparisonIso T I J n).hom =
      (iso.{u, v, v} T I n).hom ≫ (iso.{u, v, v} T J n).inv := sorry

/-- The inverse cohomological change-of-resolution map factors through abstract derived
internal-Hom cohomology. -/
@[simp, stacks 0CS5 "inverse change-of-resolution cohomology comparison"]
theorem comparisonIso_inv (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I J : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ) :
    (comparisonIso T I J n).inv =
      (iso.{u, v, v} T J n).hom ≫ (iso.{u, v, v} T I n).inv := sorry

/-- The cohomological change from a resolution to itself is the identity. -/
@[simp, stacks 0CS5 "identity change-of-resolution cohomology comparison"]
theorem comparisonIso_refl (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ) :
    comparisonIso T I I n = Iso.refl _ := sorry

/-- Reversing the cohomological change of resolution gives its inverse. -/
@[simp, stacks 0CS5 "inverse change-of-resolution cohomology comparison"]
theorem comparisonIso_symm (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I J : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ) :
    (comparisonIso T I J n).symm = comparisonIso T J I n := sorry

/-- Cohomological change-of-resolution comparisons compose transitively. -/
@[simp, stacks 0CS5 "transitivity of change-of-resolution cohomology comparisons"]
theorem comparisonIso_trans (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I J K : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ) :
    comparisonIso T I J n ≪≫ comparisonIso T J K n =
      comparisonIso T I K n := sorry

/-- The elementwise linear equivalence underlying canonical cohomological change of
resolution. -/
@[stacks 0CS5 "linear change of property-I resolution on internal-Hom cohomology"]
noncomputable def comparisonLinearEquiv
    (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I J : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ) :
    (DifferentialGradedBimodule.internalHom T I.obj).homology n ≃ₗ[R]
      (DifferentialGradedBimodule.internalHom T J.obj).homology n :=
  (comparisonIso T I J n).toLinearEquiv

/-- Applying the linear change-of-resolution comparison is compatible with the canonical
resolution-independent equivalences. -/
@[simp, stacks 0CS5 "resolution-independent cohomology under change of resolution"]
theorem linearEquiv_comparison
    (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I J : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ)
    (x : (DifferentialGradedBimodule.internalHom T I.obj).homology n) :
    linearEquiv T J n (comparisonLinearEquiv T I J n x) =
      linearEquiv T I n x := sorry

end Representability

end Resolution

end DifferentialGradedBimodule.InternalHom.Derived.Cohomology
