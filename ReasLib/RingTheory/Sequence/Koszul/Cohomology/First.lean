/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Sequence.Koszul.Relations

@[expose] public section

/-!
# A degree-one Koszul cohomology model of a finite family

This file gives the pairwise cycle-boundary object denoted `H₁(N, f)` in Stacks tag `05EE` and
its low-degree Ext sequence.  It is the degree-one cohomology model dual to the Koszul chain
complex; it is distinct from the chain-homology owner used by Koszul regularity.
@stack 05EE
-/

noncomputable section

universe u

namespace KoszulComplex.Cohomology.H1

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open CategoryTheory.Limits
open HomologicalComplex
open ModuleCat
open Ideal.Quotient (eq_zero_iff_mem)

variable {R : Type u} [CommRing R] {n : ℕ}
variable (f : Fin n → R) (N : Type u) [AddCommGroup N] [Module R N]

/-- The pairwise equations `f i • x j = f j • x i` defining degree-one Koszul cycles. -/
@[stacks 05EE "degree-one Koszul cycle condition"]
def IsCycle (x : Fin n → N) : Prop :=
  ∀ i j, f i • x j = f j • x i

/-- The map whose `(i, j)`-component is `x ↦ f i • x j - f j • x i`. -/
@[stacks 05EE "degree-one Koszul cycle map"]
def cycleMap : (Fin n → N) →ₗ[R] Fin n × Fin n → N :=
  LinearMap.pi fun ij ↦
    (DistribSMul.toLinearMap R N (f ij.1)).comp (LinearMap.proj ij.2) -
      (DistribSMul.toLinearMap R N (f ij.2)).comp (LinearMap.proj ij.1)

/-- The module of degree-one Koszul cycles for `f` with coefficients in `N`. -/
@[stacks 05EE "first Koszul cycles"]
abbrev cycles : Submodule R (Fin n → N) :=
  LinearMap.ker (cycleMap f N)

/-- The pairwise cycle equations are equivalent to membership in `cycles f N`. -/
theorem mem_cycles_iff (x : Fin n → N) :
    x ∈ cycles f N ↔ IsCycle f N x := sorry

/-- A degree-one Koszul cycle satisfies the pairwise cycle equations. -/
theorem isCycle_of_mem {x : Fin n → N} (hx : x ∈ cycles f N) :
    IsCycle f N x := sorry

/-- The degree-one boundary map `x ↦ (f i • x)ᵢ`. -/
@[stacks 05EE "degree-one Koszul boundary map"]
def boundaryMap : N →ₗ[R] Fin n → N :=
  LinearMap.pi fun i ↦ DistribSMul.toLinearMap R N (f i)

/-- The degree-one boundary map followed by the cycle map is zero. -/
theorem cycleMap_comp_boundaryMap :
    (cycleMap f N).comp (boundaryMap f N) = 0 := sorry

/-- The three-term cochain complex `N ⟶ Nⁿ ⟶ Nⁿˣⁿ` presenting degree-one Koszul cohomology. -/
@[stacks 05EE "three-term model for degree-one Koszul cohomology"]
def model : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk (boundaryMap f N) (cycleMap f N)
    (cycleMap_comp_boundaryMap f N)

/-- The degree-one Koszul cohomology object of the three-term model, denoted `H₁(N, f)` in
Stacks tag `05EE`. -/
@[stacks 05EE "degree-one Koszul cohomology"]
abbrev obj : ModuleCat R :=
  (model f N).homology

/-- The boundary map with codomain restricted to degree-one cycles. -/
@[stacks 05EE "degree-one Koszul boundary into cycles"]
abbrev boundary : N →ₗ[R] cycles f N :=
  (model f N).moduleCatToCycles

/-- The `i`th entry of the boundary of `x` is `f i • x`. -/
@[simp]
theorem boundary_apply (x : N) (i : Fin n) :
    ((boundary f N x : cycles f N) : Fin n → N) i = f i • x := sorry

/-- The explicit quotient of cycles by degree-one boundaries. -/
@[stacks 05EE "cycle-boundary presentation of degree-one Koszul cohomology"]
abbrev Presentation :=
  (model f N).moduleCatLeftHomologyData.H

/-- The canonical comparison from degree-one cohomology to its cycle-boundary presentation. -/
@[stacks 05EE "comparison with the cycle-boundary presentation"]
noncomputable abbrev presentationIso :
    obj f N ≅ ModuleCat.of R (Presentation f N) :=
  (model f N).moduleCatHomologyIso

/-- The linear map from the free module determined by a tuple in `Nⁿ`. -/
@[stacks 05EE "tuple map from the finite free module"]
def tupleHom (x : Fin n → N) : (Fin n → R) →ₗ[R] N :=
  ∑ i, (LinearMap.proj i).smulRight (x i)

/-- The tuple map evaluates a standard basis vector at the corresponding entry. -/
theorem tupleHom_basis (x : Fin n → N) (i : Fin n) :
    tupleHom N x (Pi.basisFun R (Fin n) i) = x i := sorry

/-- The relation submodule lies in the kernel of the tuple map attached to a cycle. -/
theorem relations_le_ker_tupleHom {x : Fin n → N} (hx : IsCycle f N x) :
    KoszulComplex.relations f ≤ LinearMap.ker (tupleHom N x) := sorry

/-- A Koszul cycle induces a map from the relation module. -/
@[stacks 05EE "relation-module map induced by a Koszul cycle"]
def cycleToRelation (x : cycles f N) :
    KoszulComplex.RelationModule f →ₗ[R] N :=
  (KoszulComplex.relations f).liftQ (tupleHom N x)
    (relations_le_ker_tupleHom f N (isCycle_of_mem f N x.2))

/-- Passing from cycles to maps on the relation module preserves addition. -/
theorem cycleToRelation_add (x y : cycles f N) :
    cycleToRelation f N (x + y) = cycleToRelation f N x + cycleToRelation f N y := sorry

/-- Passing from cycles to maps on the relation module preserves scalar multiplication. -/
theorem cycleToRelation_smul (a : R) (x : cycles f N) :
    cycleToRelation f N (a • x) = a • cycleToRelation f N x := sorry

/-- Cycles as a linear family of maps on the relation module. -/
@[stacks 05EE "linear map from cycles to relation-module maps"]
def cyclesToRelation :
    cycles f N →ₗ[R] (KoszulComplex.RelationModule f →ₗ[R] N) where
  toFun := cycleToRelation f N
  map_add' := cycleToRelation_add f N
  map_smul' := cycleToRelation_smul f N

/-- Evaluation on basis classes of the relation module defines a Koszul cycle. -/
theorem relationCycle_mem (g : KoszulComplex.RelationModule f →ₗ[R] N) :
    (fun i ↦ g ((KoszulComplex.relations f).mkQ (Pi.basisFun R (Fin n) i))) ∈
      cycles f N := sorry

/-- The Koszul cycle reconstructed from a map on the relation module. -/
@[stacks 05EE "Koszul cycle reconstructed from a relation-module map"]
def relationCycle (g : KoszulComplex.RelationModule f →ₗ[R] N) : cycles f N :=
  ⟨fun i ↦ g ((KoszulComplex.relations f).mkQ (Pi.basisFun R (Fin n) i)),
    relationCycle_mem f N g⟩

/-- Reconstructing a cycle from relation-module maps preserves addition. -/
theorem relationCycle_add (g h : KoszulComplex.RelationModule f →ₗ[R] N) :
    relationCycle f N (g + h) = relationCycle f N g + relationCycle f N h := sorry

/-- Reconstructing a cycle from relation-module maps preserves scalar multiplication. -/
theorem relationCycle_smul (a : R) (g : KoszulComplex.RelationModule f →ₗ[R] N) :
    relationCycle f N (a • g) = a • relationCycle f N g := sorry

/-- Reconstruct a cycle linearly from a map on the relation module. -/
@[stacks 05EE "linear reconstruction of cycles from relation-module maps"]
def relationToCycles :
    (KoszulComplex.RelationModule f →ₗ[R] N) →ₗ[R] cycles f N where
  toFun := relationCycle f N
  map_add' := relationCycle_add f N
  map_smul' := relationCycle_smul f N

/-- Reconstructing a cycle and then its relation-module map is the identity. -/
theorem cyclesToRelation_comp_relationToCycles :
    (cyclesToRelation f N).comp (relationToCycles f N) = LinearMap.id := sorry

/-- Passing to the relation module and then reading basis classes is the identity on cycles. -/
theorem relationToCycles_comp_cyclesToRelation :
    (relationToCycles f N).comp (cyclesToRelation f N) = LinearMap.id := sorry

/-- Maps from the relation module are canonically equivalent to degree-one Koszul cycles. -/
@[stacks 05EE "equivalence between relation-module maps and Koszul cycles"]
noncomputable def relationHomEquiv :
    (KoszulComplex.RelationModule f →ₗ[R] N) ≃ₗ[R] cycles f N :=
  LinearEquiv.ofLinear (relationToCycles f N) (cyclesToRelation f N)
    (relationToCycles_comp_cyclesToRelation f N)
    (cyclesToRelation_comp_relationToCycles f N)

/-- The map on the relation module remembers the cycle that induced it. -/
theorem cycleToRelation_injective : Function.Injective (cycleToRelation f N) := sorry

/-- Restricting `cycleToRelation` to the first relation kernel preserves addition of cycles. -/
theorem cycleToKernel_add (x y : cycles f N) :
    (cycleToRelation f N (x + y)).comp
        (KoszulComplex.RelationModule.kernel f).subtype =
      (cycleToRelation f N x).comp (KoszulComplex.RelationModule.kernel f).subtype +
        (cycleToRelation f N y).comp
          (KoszulComplex.RelationModule.kernel f).subtype := sorry

/-- Restricting `cycleToRelation` to the first relation kernel preserves scalar multiplication. -/
theorem cycleToKernel_smul (a : R) (x : cycles f N) :
    (cycleToRelation f N (a • x)).comp
        (KoszulComplex.RelationModule.kernel f).subtype =
      a • (cycleToRelation f N x).comp
        (KoszulComplex.RelationModule.kernel f).subtype := sorry

/-- The linear map from degree-one cycles to maps out of the first relation kernel. -/
@[stacks 05EE "map from cycles to maps out of the relation kernel"]
def cyclesToKernel :
    cycles f N →ₗ[R] (KoszulComplex.RelationModule.kernel f →ₗ[R] N) where
  toFun x :=
    (cycleToRelation f N x).comp (KoszulComplex.RelationModule.kernel f).subtype
  map_add' := cycleToKernel_add f N
  map_smul' := cycleToKernel_smul f N

/-- Degree-one boundaries vanish after restriction to the first relation kernel. -/
theorem range_boundary_le_ker_cyclesToKernel :
    LinearMap.range (boundary f N) ≤ LinearMap.ker (cyclesToKernel f N) := sorry

/-- The canonical map from degree-one Koszul cohomology to maps out of the first relation
kernel. -/
@[stacks 05EE "map from first Koszul cohomology to the relation-kernel dual"]
def toKernelHom :
    Presentation f N →ₗ[R]
      (KoszulComplex.RelationModule.kernel f →ₗ[R] N) :=
  (LinearMap.range (boundary f N)).liftQ (cyclesToKernel f N)
    (range_boundary_le_ker_cyclesToKernel f N)

/-- The quotient sequence `0 ⟶ I ⟶ R ⟶ R ⧸ I ⟶ 0` has zero composite. -/
theorem spanQuotient_comp_zero :
    (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))).toLinearMap.comp
      (Ideal.span (Set.range f)).subtype = 0 := sorry

/-- The quotient sequence attached to the ideal generated by `f`. -/
@[stacks 05EE "quotient sequence for the ideal generated by a Koszul family"]
def spanQuotientSequence : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk (Ideal.span (Set.range f)).subtype
    (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))).toLinearMap
    (spanQuotient_comp_zero f)

/-- The quotient sequence attached to the ideal generated by `f` is short exact. -/
theorem spanQuotientSequence_shortExact :
    (spanQuotientSequence f).ShortExact := sorry

/-- Evaluating a map from the generated ideal on the entries of `f` gives a cycle. -/
theorem spanHomCycle_mem (φ : Ideal.span (Set.range f) →ₗ[R] N) :
    (fun i ↦ φ ⟨f i, Ideal.subset_span ⟨i, rfl⟩⟩) ∈ cycles f N := sorry

/-- The cycle obtained by evaluating a map from the generated ideal on the entries of `f`. -/
@[stacks 05EE "cycle obtained from a map on the generated ideal"]
def spanHomCycle (φ : Ideal.span (Set.range f) →ₗ[R] N) : cycles f N :=
  ⟨fun i ↦ φ ⟨f i, Ideal.subset_span ⟨i, rfl⟩⟩, spanHomCycle_mem f N φ⟩

/-- Evaluation on the entries of `f` preserves addition. -/
theorem spanHomCycle_add (φ ψ : Ideal.span (Set.range f) →ₗ[R] N) :
    spanHomCycle f N (φ + ψ) = spanHomCycle f N φ + spanHomCycle f N ψ := sorry

/-- Evaluation on the entries of `f` preserves scalar multiplication. -/
theorem spanHomCycle_smul (a : R) (φ : Ideal.span (Set.range f) →ₗ[R] N) :
    spanHomCycle f N (a • φ) = a • spanHomCycle f N φ := sorry

/-- Evaluation on the entries of `f` as a linear map into the cycle module. -/
@[stacks 05EE "evaluation on generators as a map into Koszul cycles"]
def spanHomToCycles :
    (Ideal.span (Set.range f) →ₗ[R] N) →ₗ[R] cycles f N where
  toFun := spanHomCycle f N
  map_add' := spanHomCycle_add f N
  map_smul' := spanHomCycle_smul f N

/-- The scalar-action map `N ⟶ Hom_R(I, N)` for `I = Ideal.span (Set.range f)`. -/
@[stacks 05EE "scalar-action map into maps from the generated ideal"]
def spanToHom :
    N →ₗ[R] (Ideal.span (Set.range f) →ₗ[R] N) :=
  ((LinearMap.lsmul R N).comp (Ideal.span (Set.range f)).subtype).flip

/-- Evaluation of a map from the generated ideal agrees with its factorization through the
relation module. -/
theorem spanHom_cycleToRelation (φ : Ideal.span (Set.range f) →ₗ[R] N) :
    cycleToRelation f N (spanHomToCycles f N φ) =
      φ.comp (KoszulComplex.RelationModule.toSpan f) := sorry

/-- Evaluation on generators followed by the quotient of cycles by boundaries. -/
@[stacks 05EE "map from generated-ideal homomorphisms to the Koszul presentation"]
def spanHomToPresentation :
    (Ideal.span (Set.range f) →ₗ[R] N) →ₗ[R] Presentation f N :=
  (LinearMap.range (boundary f N)).mkQ.comp (spanHomToCycles f N)

/-- The kernel of the map to the cycle-boundary presentation consists exactly of scalar-action
maps. -/
theorem ker_spanHomToPresentation :
    LinearMap.ker (spanHomToPresentation f N) =
      LinearMap.range (spanToHom f N) := sorry

/-- The image of maps from the generated ideal is the kernel of the map from degree-one cohomology
to maps out of the first relation kernel. -/
theorem range_spanHomToPresentation :
    LinearMap.range (spanHomToPresentation f N) =
      LinearMap.ker (toKernelHom f N) := sorry

/-- The connecting map `Hom_R(I, N) ⟶ Ext¹_R(R ⧸ I, N)` for the quotient sequence. -/
@[stacks 05EE "connecting map from generated-ideal homomorphisms to Ext one"]
noncomputable def spanHomToExt :
    (Ideal.span (Set.range f) →ₗ[R] N) →ₗ[R]
      Ext (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) (ModuleCat.of R N) 1 :=
  ((spanQuotientSequence_shortExact f).extClass.precompOfLinear
      R (ModuleCat.of R N) (Nat.add_zero 1)) ∘ₗ
    (((Ext.linearEquiv₀ :
        Ext (ModuleCat.of R (Ideal.span (Set.range f))) (ModuleCat.of R N) 0 ≃ₗ[R]
          (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N)).symm.toLinearMap) ∘ₗ
      ((ModuleCat.homLinearEquiv :
          (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
            (Ideal.span (Set.range f) →ₗ[R] N)).symm.toLinearMap))

/-- The connecting map for the generated-ideal quotient sequence is surjective. -/
theorem spanHomToExt_surjective : Function.Surjective (spanHomToExt f N) := sorry

/-- Scalar-action maps lie in the kernel of the connecting map. -/
theorem spanHomToExt_comp_spanToHom :
    spanHomToExt f N ∘ₗ spanToHom f N = 0 := sorry

/-- The kernel of the connecting map consists exactly of scalar-action maps. -/
theorem ker_spanHomToExt :
    LinearMap.ker (spanHomToExt f N) = LinearMap.range (spanToHom f N) := sorry

/-- The connecting map and the cycle-presentation map have the same kernel. -/
theorem ker_spanHomToExt_le_ker_spanHomToPresentation :
    LinearMap.ker (spanHomToExt f N) ≤
      LinearMap.ker (spanHomToPresentation f N) := sorry

/-- The map from the quotient of `Hom_R(I, N)` by the connecting-map kernel to degree-one
cohomology. -/
@[stacks 05EE "quotient-kernel comparison with first Koszul cohomology"]
noncomputable def kerToPresentation :
    ((Ideal.span (Set.range f) →ₗ[R] N) ⧸ LinearMap.ker (spanHomToExt f N)) →ₗ[R]
      Presentation f N :=
  (LinearMap.ker (spanHomToExt f N)).liftQ (spanHomToPresentation f N)
    (ker_spanHomToExt_le_ker_spanHomToPresentation f N)

/-- The canonical injection `Ext¹_R(R ⧸ I, N) ⟶ H₁(N, f)`, where the target is the `05EE`
degree-one cohomology object. -/
@[stacks 05EE "canonical injection from Ext one to first Koszul cohomology"]
noncomputable def extToPresentation :
    Ext (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) (ModuleCat.of R N) 1 →ₗ[R]
      Presentation f N :=
  kerToPresentation f N ∘ₗ
    ((spanHomToExt f N).quotKerEquivOfSurjective
      (spanHomToExt_surjective f N)).symm.toLinearMap

/-- The map from `Ext¹` to the cycle-boundary presentation is characterized on representatives
coming from maps out of the generated ideal. -/
theorem extToPresentation_comp_spanHomToExt :
    extToPresentation f N ∘ₗ spanHomToExt f N = spanHomToPresentation f N := sorry

/-- The representative formula uniquely determines the map from `Ext¹` to the cycle-boundary
presentation.  This is the public independence API for the chosen inverse hidden in
`extToPresentation`. -/
theorem extToPresentation_unique
    (φ : Ext (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) (ModuleCat.of R N) 1 →ₗ[R]
      Presentation f N)
    (hφ : φ ∘ₗ spanHomToExt f N = spanHomToPresentation f N) :
    φ = extToPresentation f N := sorry

/-- The canonical map from `Ext¹_R(R ⧸ I, N)` to degree-one Koszul cohomology is injective. -/
theorem extToPresentation_injective :
    Function.Injective (extToPresentation f N) := sorry

/-- The image of `Ext¹_R(R ⧸ I, N)` is the kernel of the next map in the low-degree sequence. -/
theorem range_extToPresentation :
    LinearMap.range (extToPresentation f N) =
      LinearMap.ker (toKernelHom f N) := sorry

/-- The canonical map from degree-one Koszul cohomology to maps out of the relation kernel. -/
@[stacks 05EE "canonical map from first Koszul cohomology to relation-kernel maps"]
noncomputable def toKernel :
    obj f N ⟶ ModuleCat.of R (KoszulComplex.RelationModule.kernel f →ₗ[R] N) :=
  (presentationIso f N).hom ≫ ModuleCat.ofHom (toKernelHom f N)

/-- The canonical map from `Ext¹_R(R ⧸ I, N)` to degree-one Koszul cohomology. -/
@[stacks 05EE "canonical map from Ext one to first Koszul cohomology"]
noncomputable def extTo :
    ModuleCat.of R
        (Ext (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) (ModuleCat.of R N) 1) ⟶
      obj f N :=
  ModuleCat.ofHom (extToPresentation f N) ≫ (presentationIso f N).inv

/-- The two maps in the low-degree Ext sequence compose to zero. -/
theorem extTo_toKernel : extTo f N ≫ toKernel f N = 0 := sorry

/-- The low-degree sequence
`0 ⟶ Ext¹_R(R ⧸ I, N) ⟶ H₁(N, f) ⟶ Hom_R(K, N)`. -/
@[stacks 05EE "low-degree Ext sequence for degree-one Koszul cohomology"]
def extSequence : ShortComplex (ModuleCat R) :=
  ShortComplex.mk (extTo f N) (toKernel f N) (extTo_toKernel f N)

/-- Lemma 15.90.6 (Tag `05EE`): the left map in the low-degree Ext sequence is a monomorphism. -/
@[stacks 05EE "Ext embeds into degree-one Koszul cohomology"]
instance extSequence_mono : Mono (extSequence f N).f := sorry

/-- Lemma 15.90.6 (Tag `05EE`): the low-degree Ext sequence is exact at the degree-one Koszul
cohomology object. -/
@[stacks 05EE "exactness of the degree-one Koszul cohomology sequence"]
theorem extSequence_exact : (extSequence f N).Exact := sorry

end KoszulComplex.Cohomology.H1
