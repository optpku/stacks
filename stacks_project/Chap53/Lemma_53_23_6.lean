/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail.Terminal
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.SchemeOverField.RationalTail
open AlgebraicGeometry.SchemeOverField.RationalTail.ContractionChain
open AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme

noncomputable section

universe u

/- Lemma 53.23.6 (1): a terminating rational-tail contraction chain in genus zero has
endpoint an irreducible plane conic. -/
@[stacks 0E3L] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.ContractionChain.endpointPlaneConic :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) {Y : SchemeOverField k}
    (chain : ContractionChain X Y) (h_no_tail : ¬ Nonempty (RationalTail Y))
    (h_genus : genus X h_dimension h_global = 0),
    ∃ (Z : (ProjectiveSpace.scheme k 2).IdealSheafData)
      (F : MvPolynomial (Fin 3) k),
      IsIntegral Z.subscheme ∧
        Nonempty (Y ≅ Over.mk (Z.subschemeι ≫ ProjectiveSpace.toSpec k 2)) ∧
        HasHomogeneousEquation 2 Z F ∧ F.totalDegree = 2)

/- Lemma 53.23.6 (2): a terminating rational-tail contraction chain in genus one has
trivial dualizing module on its endpoint. -/
@[stacks 0E3L] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.ContractionChain.endpointDualizingIso :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) {Y : SchemeOverField k}
    (chain : ContractionChain X Y) (h_no_tail : ¬ Nonempty (RationalTail Y))
    (h_genus : genus X h_dimension h_global = 1),
    Nonempty
      (endpointDualizingModule chain ≅
        (SheafOfModules.unit Y.left.ringCatSheaf : Y.left.Modules)))

/- Lemma 53.23.6 (3): in genus at least two, every integral tensor power of the endpoint
dualizing module of exponent at least two is globally generated. -/
@[stacks 0E3L] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.ContractionChain.endpointTensorPowerGloballyGenerated :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) {Y : SchemeOverField k}
    (chain : ContractionChain X Y) (h_no_tail : ¬ Nonempty (RationalTail Y))
    (h_genus : (2 : ℕ) ≤ genus X h_dimension h_global)
    (m : ℤ) (h_m : (2 : ℤ) ≤ m),
    SheafOfModules.IsGloballyGenerated
      (endpointDualizingPower X h_dimension h_global h_nodal chain m))

/- Lemma 53.23.6 (4): in positive genus, any two terminal rational-tail contraction chains
have uniquely compatibly isomorphic endpoints. -/
@[stacks 0E3L] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.ContractionChain.uniqueEndpoint :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) {Y Z : SchemeOverField k}
    (chainY : ContractionChain X Y) (h_Y : ¬ Nonempty (RationalTail Y))
    (chainZ : ContractionChain X Z) (h_Z : ¬ Nonempty (RationalTail Z))
    (h_genus : (1 : ℕ) ≤ genus X h_dimension h_global),
    ∃! e : Y ≅ Z, chainY.map ≫ e.hom = chainZ.map)

/- Lemma 53.23.6 (5): after a field extension, the base-changed contraction morphism is
represented by a concrete rational-tail contraction chain. -/
@[stacks 0E3L] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.ContractionChain.existsBaseChange :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) {Y : SchemeOverField k}
    (chain : ContractionChain X Y) (h_no_tail : ¬ Nonempty (RationalTail Y))
    (h_genus : (1 : ℕ) ≤ genus X h_dimension h_global)
    (K : Type u) [Field K] [Algebra k K],
    ∃ chainK : ContractionChain (FieldExtension.Over.baseChange k K X)
        (FieldExtension.Over.baseChange k K Y),
      chainK.map = (FieldExtension.Over.functor k K).map chain.map)

/- Lemma 53.23.6 (6): rational tails do not reappear on the endpoint after extending the
ground field. -/
@[stacks 0E3L] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.ContractionChain.baseChangeNoTail :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) {Y : SchemeOverField k}
    (chain : ContractionChain X Y) (h_no_tail : ¬ Nonempty (RationalTail Y))
    (h_genus : (1 : ℕ) ≤ genus X h_dimension h_global)
    (K : Type u) [Field K] [Algebra k K],
    ¬ Nonempty (RationalTail (FieldExtension.Over.baseChange k K Y)))

/- Lemma 53.23.6 (7): every terminal base-changed contraction chain has a unique endpoint
isomorphism compatible with the base-changed original contraction morphism. -/
@[stacks 0E3L] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.ContractionChain.commutesWithBaseChange :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) {Y : SchemeOverField k}
    (chain : ContractionChain X Y) (h_no_tail : ¬ Nonempty (RationalTail Y))
    (h_genus : (1 : ℕ) ≤ genus X h_dimension h_global)
    (K : Type u) [Field K] [Algebra k K] {Z : SchemeOverField K}
    (chainK : ContractionChain (FieldExtension.Over.baseChange k K X) Z)
    (h_Z : ¬ Nonempty (RationalTail Z)),
    ∃! e : FieldExtension.Over.baseChange k K Y ≅ Z,
      (FieldExtension.Over.functor k K).map chain.map ≫ e.hom = chainK.map)
