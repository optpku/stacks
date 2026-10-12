/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.Genus

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 55.9.10: In Situation 55.9.3, if `d` is the gcd of the special-fibre
multiplicities and `D` is the normalized effective Cartier divisor, then
`1 - g_C = d * [κ : k] * (1 - g_D)`, where `κ` is the global-sections field of `D`.
The two genera are the degree-one cohomology finranks of the structure sheaves:
`g_C` over `K` via `C.hom`, and `g_D` over `κ` via `D.subscheme.toSpecΓ`. -/
@[stacks 0C69]
#check (AlgebraicGeometry.Scheme.Hom.genusFormula_primitiveSpecialFiber :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))),
    (1 : ℤ) - (Scheme.Hom.cohomologyFinrank C.hom
      (SheafOfModules.unit C.left.ringCatSheaf : C.left.Modules) 1 : ℤ) =
      (Scheme.Hom.specialFiberMultiplicityGcd f n components : ℤ) *
        (Module.finrank
          ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
          (Scheme.Hom.globalSectionsAlg
            (Scheme.Hom.primitiveSpecialFiberToResidueField f n components) :
            CommAlgCat ((Spec (CommRingCat.of R)).residueField
              (IsLocalRing.closedPoint R))) : ℤ) *
        ((1 : ℤ) - (Scheme.Hom.cohomologyFinrank
          (Scheme.Hom.primitiveSpecialFiberDivisor f n components).subscheme.toSpecΓ
          (SheafOfModules.unit
            (Scheme.Hom.primitiveSpecialFiberDivisor f n components).subscheme.ringCatSheaf :
            (Scheme.Hom.primitiveSpecialFiberDivisor f n components).subscheme.Modules) 1 : ℤ)))
