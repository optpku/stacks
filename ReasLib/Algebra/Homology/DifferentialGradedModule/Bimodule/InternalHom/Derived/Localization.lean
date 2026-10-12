/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.KProjective
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction

/-!
# Underived Models for Derived Internal Hom

When fixed-source internal Hom already sends quasi-isomorphisms to isomorphisms, its derived
unit is invertible. K-projectivity of the source as a right module is the intrinsic condition;
property P is a reusable sufficient criterion.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedBimodule.InternalHom

variable {R : Type u} [CommRing R]

section General

variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}

/-- If fixed-source internal Hom already inverts quasi-isomorphisms, its canonical comparison
with derived internal Hom is an isomorphism of functors. -/
@[stacks 0BYW "derived internal-Hom unit for a localizing source"]
theorem derivedUnit_isIso_of_inverts
    (T : DifferentialGradedBimodule.{u, v, w, x} A B)
    (hT : (DifferentialGradedModule.quasiIso B).IsInvertedBy
      (derivedSourceFunctor T)) :
    IsIso (derivedUnit T) := sorry

/-- A total derived internal-Hom functor whose source already inverts quasi-isomorphisms is
canonically isomorphic to the direct localization lift of its source functor. -/
@[stacks 0BYW "derived internal Hom as a localization lift"]
noncomputable def derivedFunctorIsoLiftOfInverts
    (T : DifferentialGradedBimodule.{u, v, w, x} A B)
    (hT : (DifferentialGradedModule.quasiIso B).IsInvertedBy
      (derivedSourceFunctor T)) :
    derivedFunctor T ≅
      Localization.lift (derivedSourceFunctor T) hT
        (DifferentialGradedModule.Derived.Q B) :=
  CategoryTheory.Functor.RightDerived.totalIsoLiftOfIso
    (F := derivedSourceFunctor T) (G := derivedSourceFunctor T)
    (L := DifferentialGradedModule.Derived.Q B)
    (DifferentialGradedModule.quasiIso B) hT (Iso.refl _)

/-- A derived internal-Hom functor whose source functor inverts quasi-isomorphisms is isomorphic
to the direct localization lift of that source functor. -/
@[stacks 0BYW "derived internal-Hom lift comparison"]
theorem derivedFunctor_isIsomorphic_lift_of_inverts
    (T : DifferentialGradedBimodule.{u, v, w, x} A B)
    (hT : (DifferentialGradedModule.quasiIso B).IsInvertedBy
      (derivedSourceFunctor T)) :
    IsIsomorphic (derivedFunctor T)
      (Localization.lift (derivedSourceFunctor T) hT
        (DifferentialGradedModule.Derived.Q B)) := sorry

end General

/- The regular-cell K-projective and property-P owners require the DGA and DG-module carriers
to lie in the same universe; that common universe need not be the base-ring universe. -/
section SameCarrier

variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, v} R}

/-- Fixed-source internal Hom from a K-projective right `B`-module sends quasi-isomorphisms to
isomorphisms after localization in right DG `A`-modules. -/
@[stacks 0BYW "K-projective source preserves quasi-isomorphisms for derived internal Hom"]
theorem derivedSourceFunctor_isInvertedBy_of_kProjective
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    (hT : DifferentialGradedModule.Homotopy.kProjective B
      ((DifferentialGradedModule.toK B).obj T.toRightModule)) :
    (DifferentialGradedModule.quasiIso B).IsInvertedBy
      (derivedSourceFunctor T) := sorry

/-- Lemma 22.31.5 (0BYW): if the source bimodule is K-projective as a right `B`-module, ordinary
fixed-source internal Hom computes derived internal Hom, functorially in the target. -/
@[stacks 0BYW "K-projective source computes derived internal Hom"]
theorem derivedUnit_isIso_of_kProjective
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    (hT : DifferentialGradedModule.Homotopy.kProjective B
      ((DifferentialGradedModule.toK B).obj T.toRightModule)) :
    IsIso (derivedUnit T) := sorry

/-- A source bimodule with property P as a right `B`-module computes derived internal Hom without
a replacement. -/
@[stacks 0BYW "property-P source computes derived internal Hom"]
theorem derivedUnit_isIso_of_hasPropertyP
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    (hT : DifferentialGradedModule.HasPropertyP B T.toRightModule) :
    IsIso (derivedUnit T) := sorry

end SameCarrier

end DifferentialGradedBimodule.InternalHom
