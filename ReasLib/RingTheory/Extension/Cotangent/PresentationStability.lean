module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.ChainComplex.Stability
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Concentration

/-!
# Stable Cotangent Modules of Algebra Presentations

@stack 00S5

This leaf packages the presentation-independent stable equivalence of
conormal modules.  The chain-complex stabilization is owned by
`ChainComplex.HomotopyEquiv`; this file only specializes it to canonical
maps between algebra presentations and, separately, to free
coordinates.
-/

@[expose] public section

open Algebra
open CategoryTheory

universe u v w

noncomputable section

namespace Algebra.Generators.Cotangent

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {ι ι' : Type w}

/-- The stable linear equivalence on the degree-one/degree-zero terms of the naive cotangent
complexes of two algebra presentations. -/
@[stacks 00S5 "termwise cotangent stabilization"]
noncomputable def complexTermStableEquiv
    (P : Generators R S ι) (Q : Generators R S ι') :
    ((Extension.NaiveCotangent.complex P.toExtension).X 1 ×
      (Extension.NaiveCotangent.complex Q.toExtension).X 0) ≃ₗ[S]
      ((Extension.NaiveCotangent.complex Q.toExtension).X 1 ×
        (Extension.NaiveCotangent.complex P.toExtension).X 0) :=
  ((ModuleCat.biprodIsoProd ((Extension.NaiveCotangent.complex P.toExtension).X 1)
      ((Extension.NaiveCotangent.complex Q.toExtension).X 0)).symm ≪≫
    ChainComplex.HomotopyEquiv.stableBiprodIso
      (Extension.NaiveCotangent.generatorsHomotopyEquiv P Q)
      (Extension.NaiveCotangent.componentSuccSuccIsZero P.toExtension 0)
      (Extension.NaiveCotangent.componentSuccSuccIsZero Q.toExtension 0) ≪≫
    ModuleCat.biprodIsoProd ((Extension.NaiveCotangent.complex Q.toExtension).X 1)
      ((Extension.NaiveCotangent.complex P.toExtension).X 0)).toLinearEquiv

/-- The stable linear equivalence on the lifted conormal modules of two algebra presentations.
It transports `complexTermStableEquiv` through the canonical degree-one and degree-zero
identifications of the naive cotangent complex. -/
@[stacks 00S5 "lifted cotangent stabilization"]
noncomputable def liftStableEquiv
    (P : Generators R S ι) (Q : Generators R S ι') :
    (Extension.NaiveCotangent.Lift P.toExtension × Q.toExtension.CotangentSpace) ≃ₗ[S]
      (Extension.NaiveCotangent.Lift Q.toExtension × P.toExtension.CotangentSpace) :=
  (LinearEquiv.prodCongr
      (Extension.NaiveCotangent.componentOneIso P.toExtension).toLinearEquiv.symm
      (Extension.NaiveCotangent.componentZeroIso Q.toExtension).toLinearEquiv.symm).trans <|
    (complexTermStableEquiv P Q).trans <|
      LinearEquiv.prodCongr
        (Extension.NaiveCotangent.componentOneIso Q.toExtension).toLinearEquiv
        (Extension.NaiveCotangent.componentZeroIso P.toExtension).toLinearEquiv

/-- The presentation-independent stable linear equivalence of conormal and cotangent-space
modules. -/
@[stacks 00S5 "cotangent stable equivalence"]
noncomputable def stableEquiv
    (P : Generators R S ι) (Q : Generators R S ι') :
    (P.toExtension.Cotangent × Q.toExtension.CotangentSpace) ≃ₗ[S]
      (Q.toExtension.Cotangent × P.toExtension.CotangentSpace) :=
  (LinearEquiv.prodCongr
      (Extension.NaiveCotangent.liftEquiv P.toExtension).symm
      (LinearEquiv.refl S Q.toExtension.CotangentSpace)).trans <|
    (liftStableEquiv P Q).trans <|
      LinearEquiv.prodCongr
        (Extension.NaiveCotangent.liftEquiv Q.toExtension)
        (LinearEquiv.refl S P.toExtension.CotangentSpace)

/-- Lemma 10.134.15, tag `00S5`: after identifying cotangent spaces with their canonical
free bases, two algebra presentations have stably equivalent conormal modules. -/
@[stacks 00S5 "free-coordinate cotangent stabilization"]
noncomputable def stableEquivFree
    (P : Generators R S ι) (Q : Generators R S ι') :
    (P.toExtension.Cotangent × (ι' →₀ S)) ≃ₗ[S]
      (Q.toExtension.Cotangent × (ι →₀ S)) :=
  (LinearEquiv.prodCongr
      (LinearEquiv.refl S P.toExtension.Cotangent)
      Q.cotangentSpaceBasis.repr.symm).trans <|
    (stableEquiv P Q).trans <|
      LinearEquiv.prodCongr
        (LinearEquiv.refl S Q.toExtension.Cotangent)
        P.cotangentSpaceBasis.repr

end Algebra.Generators.Cotangent
