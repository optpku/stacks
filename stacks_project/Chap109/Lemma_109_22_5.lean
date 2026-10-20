module

public import ReasLib.AlgebraicGeometry.Curve.StableOfGenus
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.SchemeOverField
open Scheme.DerivedQCoh.ProperDualizingComplex
open SheafOfModules
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 109.22.5: a proper scheme of dimension at most one over a field is a
stable curve if and only if it is a stable family of some genus `g ≥ 2`,
equivalently at-worst-nodal of genus `g` with no rational tails or bridges,
equivalently with ample canonical dualizing module. -/
@[stacks 0E78] #check (AlgebraicGeometry.exists_isStableFamilyOfGenus_iff :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1),
    isStableCurve X ↔ ∃ g : ℕ, IsStableFamilyOfGenus (g + 2) X.hom)

#check (AlgebraicGeometry.eq_of_isStableFamilyOfGenus :
  ∀ {X S : Scheme.{u}} [Nonempty S] {f : X ⟶ S} {g g' : ℕ},
    IsStableFamilyOfGenus g f → IsStableFamilyOfGenus g' f → g = g')

#check (AlgebraicGeometry.isStableFamilyOfGenus_iff_atWorstNodal_genus :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) (hg : 2 ≤ g),
    IsStableFamilyOfGenus g X.hom ↔
      atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          genus X hdim1 hΓ = g ∧
            ¬ Nonempty (RationalTail X) ∧ ¬ Nonempty (RationalBridge X))

#check (AlgebraicGeometry.isStableFamilyOfGenus_iff_curveDualizingModule_isAmple :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) (hg : 2 ≤ g),
    IsStableFamilyOfGenus g X.hom ↔
      atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          genus X hdim1 hΓ = g ∧
            Scheme.Modules.isAmpleObject (curveDualizingModule X.hom))
