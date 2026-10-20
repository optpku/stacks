module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.DualizingSemiampleness
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme
open AlgebraicGeometry.Scheme
open Scheme.DerivedQCoh.ProperDualizingComplex

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.23.5 (1): a proper one-dimensional at-worst-nodal scheme over a field,
with only constant global functions and no rational tail, is an irreducible plane conic
when its genus is zero. -/
@[stacks 0E3K] #check
  (AlgebraicGeometry.SchemeOverField.exists_irreduciblePlaneConic_of_genus_zero : ∀ {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (h_no_tail : ¬ Nonempty (RationalTail X))
    (h_genus : genus X h_dimension h_global = 0),
    ∃ (Z : (ProjectiveSpace.scheme k 2).IdealSheafData)
      (F : MvPolynomial (Fin 3) k),
      IsIntegral Z.subscheme ∧
        Nonempty (X ≅ Over.mk (Z.subschemeι ≫ ProjectiveSpace.toSpec k 2)) ∧
        HasHomogeneousEquation 2 Z F ∧ F.totalDegree = 2)

/- Lemma 53.23.5 (2): under the same hypotheses in genus zero, the inverse tensor
power of the dualizing module is relatively very ample over the ground field. -/
@[stacks 0E3K] #check
  (AlgebraicGeometry.SchemeOverField.inverseDualizingModule_relativelyVeryAmple_of_genus_zero : ∀ {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (h_no_tail : ¬ Nonempty (RationalTail X))
    (h_genus : genus X h_dimension h_global = 0),
    let _ : EquidimensionalSpace X.left :=
      equidimensionalSpace_of_dim_one_of_globalSectionsMap_bijective X h_dimension h_global
    let _ : Fact (topologicalKrullDim X.left = 1) := ⟨h_dimension⟩
    let _ : Fact (atWorstNodal X) := ⟨h_nodal⟩
    RelativelyVeryAmple X.hom
      (Scheme.Modules.tensorPowerInt (dualizingModule X.hom) (-1)))

/- Lemma 53.23.5 (3): under the same hypotheses in genus one, the dualizing module
is isomorphic to the structure module. -/
@[stacks 0E3K] #check
  (AlgebraicGeometry.SchemeOverField.dualizingModule_isomorphic_unit_of_genus_one : ∀ {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (h_no_tail : ¬ Nonempty (RationalTail X))
    (h_genus : genus X h_dimension h_global = 1),
    Nonempty
      (dualizingModule X.hom ≅
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)))

/- Lemma 53.23.5 (4): under the same hypotheses in genus at least two, every
integral tensor power of the dualizing module of exponent at least two is globally generated. -/
@[stacks 0E3K] #check
  (AlgebraicGeometry.SchemeOverField.dualizingModule_tensorPower_isGloballyGenerated_of_genus_ge_two :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (h_no_tail : ¬ Nonempty (RationalTail X))
    (h_genus : (2 : ℕ) ≤ genus X h_dimension h_global)
    (m : ℤ) (h_m : (2 : ℤ) ≤ m),
    let _ : EquidimensionalSpace X.left :=
      equidimensionalSpace_of_dim_one_of_globalSectionsMap_bijective X h_dimension h_global
    let _ : Fact (topologicalKrullDim X.left = 1) := ⟨h_dimension⟩
    let _ : Fact (atWorstNodal X) := ⟨h_nodal⟩
    SheafOfModules.IsGloballyGenerated
      (Scheme.Modules.tensorPowerInt (dualizingModule X.hom) m))

end AlgebraicGeometry.SchemeOverField
