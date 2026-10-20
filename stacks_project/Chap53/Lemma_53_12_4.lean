/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Curve.RiemannHurwitz
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Curve
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry BigOperators

universe u

/- Lemma 53.12.4 (1): for the Riemann--Hurwitz setup, the genus correction is the sum over
closed points of the multiplicities of the Kähler different, weighted by residue field degrees. -/
@[stacks 0C1F] #check
  (AlgebraicGeometry.Curve.riemannHurwitz_eq_finsum_multiplicity :
    ∀ {k : Type u} [Field k] (X Y : SchemeOverField k) [Curve X] [Curve Y]
      [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
      [LocallyOfFiniteType f.left] [IsDominant f.left]
      (h_finite : f.left.FiniteFunctionFieldExtension)
      (h_separable : f.left.SeparableFunctionFieldExtension)
      (hΓX : Function.Bijective (globalSectionsMap X.hom))
      (hΓY : Function.Bijective (globalSectionsMap Y.hom)) (gX gY : ℕ)
      (h_genusX : gX = genus X (AlgebraicGeometry.topologicalKrullDim_eq_one X) hΓX)
      (h_genusY : gY = genus Y (AlgebraicGeometry.topologicalKrullDim_eq_one Y) hΓY),
      2 * (gX : ℤ) - 2 =
        (2 * (gY : ℤ) - 2) * (f.left.inducedFunctionFieldDegree : ℤ) +
          ∑ᶠ x : closedPoints X.left,
            (kaehlerDifferentMultiplicity f x : ℤ) * (X.hom.residueDegree x.1 : ℤ))

/- Lemma 53.12.4 (2): the multiplicity of the Kähler different equals the length of the stalk of
the relative differential module over the local ring. -/
@[stacks 0C1F] #check
  (AlgebraicGeometry.Curve.kaehlerDifferentMultiplicity_eq_relativeDifferentialsLength :
    ∀ {k : Type u} [Field k] {X Y : SchemeOverField k} [Curve X] [Curve Y]
      [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
      [LocallyOfFiniteType f.left] [IsDominant f.left]
      (h_finite : f.left.FiniteFunctionFieldExtension)
      (h_separable : f.left.SeparableFunctionFieldExtension)
      (hΓX : Function.Bijective (globalSectionsMap X.hom))
      (hΓY : Function.Bijective (globalSectionsMap Y.hom)) (x : closedPoints X.left),
      (kaehlerDifferentMultiplicity f x : ℕ∞) =
        Module.length (stalkRing X x.1)
          (RingedSpace.stalkModuleCat (Ω[f.left.toShHom]) x.1))

/- Lemma 53.12.4 (3): the multiplicity at a closed point is at least the ramification index minus
one, where the index is computed from the induced local-ring map. -/
@[stacks 0C1F] #check
  (AlgebraicGeometry.Curve.ramificationIndexAt_sub_one_le_multiplicity :
    ∀ {k : Type u} [Field k] {X Y : SchemeOverField k} [Curve X] [Curve Y]
      [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
      [LocallyOfFiniteType f.left] [IsDominant f.left]
      (h_finite : f.left.FiniteFunctionFieldExtension)
      (h_separable : f.left.SeparableFunctionFieldExtension)
      (hΓX : Function.Bijective (globalSectionsMap X.hom))
      (hΓY : Function.Bijective (globalSectionsMap Y.hom)) (x : closedPoints X.left),
      kaehlerDifferentMultiplicity f x ≥ f.left.ramificationIndexAt x.1 - 1)

/- Lemma 53.12.4 (4): equality in the ramification bound holds exactly when the residue-field
extension is separable and the ramification index is prime to every characteristic of the target
residue field. -/
@[stacks 0C1F] #check
  (AlgebraicGeometry.Curve.multiplicity_eq_ramificationIndexAt_sub_one_iff_tame :
    ∀ {k : Type u} [Field k] {X Y : SchemeOverField k} [Curve X] [Curve Y]
      [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
      [LocallyOfFiniteType f.left] [IsDominant f.left]
      (h_finite : f.left.FiniteFunctionFieldExtension)
      (h_separable : f.left.SeparableFunctionFieldExtension)
      (hΓX : Function.Bijective (globalSectionsMap X.hom))
      (hΓY : Function.Bijective (globalSectionsMap Y.hom)) (x : closedPoints X.left),
      (kaehlerDifferentMultiplicity f x = f.left.ramificationIndexAt x.1 - 1) ↔
        (Algebra.IsSeparable (Y.left.residueField (f.left x.1))
            (X.left.residueField x.1) ∧
          DVR.Field.PrimeToChar (Y.left.residueField (f.left x.1))
            (f.left.ramificationIndexAt x.1)))
