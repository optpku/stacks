module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite irreducible components on quasi-compact opens

This leaf packages the finiteness condition on irreducible components of every
quasi-compact open subscheme.  It is useful independently of normalization or
rational-map constructions.
-/

@[expose] public section

open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme has finitely many irreducible components on each quasi-compact
open subscheme. -/
class HasFiniteIrreducibleComponentsOnCompactOpens (X : Scheme.{u}) : Prop where
  /-- The irreducible components of a quasi-compact open are finite. -/
  finite_irreducibleComponents (U : CompactOpens X) :
    (irreducibleComponents U).Finite

namespace HasFiniteIrreducibleComponentsOnCompactOpens

/-- A scheme with finitely many irreducible components has finitely many irreducible components
on every quasi-compact open subscheme. -/
instance instOfFiniteIrreducibleComponents (X : Scheme.{u})
    [Finite (irreducibleComponents X)] :
    HasFiniteIrreducibleComponentsOnCompactOpens X := by
  constructor
  intro U
  let f : U → X := Subtype.val
  have hf : Topology.IsOpenEmbedding f := U.isOpen.isOpenEmbedding_subtypeVal
  let componentMap : irreducibleComponents U → irreducibleComponents X := fun Z ↦
    ⟨closure (f '' Z.1), by
      refine ⟨(Z.2.1.image f hf.continuous.continuousOn).closure, ?_⟩
      intro T hT hZT
      have hmeet : (closure T ∩ Set.range f).Nonempty := by
        obtain ⟨z, hz⟩ := Z.2.1.nonempty
        exact ⟨f z, subset_closure (hZT (subset_closure ⟨z, hz, rfl⟩)), z, rfl⟩
      have hpre : IsIrreducible (f ⁻¹' closure T) := hT.closure.preimage hf hmeet
      have hsub : Z.1 ⊆ f ⁻¹' closure T := fun z hz ↦
        subset_closure (hZT (subset_closure ⟨z, hz, rfl⟩))
      have heq : Z.1 = f ⁻¹' closure T :=
        Set.Subset.antisymm hsub (Z.2.2 hpre hsub)
      calc
        T ⊆ closure T := subset_closure
        _ = closure (f '' (f ⁻¹' closure T)) :=
          (closure_image_preimage_of_isPreirreducible f hf.isOpenMap (closure T)
            (by
              obtain ⟨_, ht, z, rfl⟩ := hmeet
              exact ⟨z, ht⟩)
            hT.closure.2 isClosed_closure).symm
        _ = closure (f '' Z.1) := by rw [heq]⟩
  have recover (Z : irreducibleComponents U) :
      f ⁻¹' (componentMap Z).1 = Z.1 := by
    change f ⁻¹' closure (f '' Z.1) = Z.1
    rw [hf.isOpenMap.preimage_closure_eq_closure_preimage hf.continuous,
      Set.preimage_image_eq _ hf.injective,
      (isClosed_of_mem_irreducibleComponents Z.1 Z.2).closure_eq]
  exact @Finite.of_injective _ _ inferInstance componentMap fun Z W hZW ↦ by
    apply Subtype.ext
    rw [← recover Z, hZW, recover W]

/-- A locally Noetherian scheme has finitely many irreducible components on every compact
open. -/
instance instOfIsLocallyNoetherian (X : Scheme.{u}) [IsLocallyNoetherian X] :
    HasFiniteIrreducibleComponentsOnCompactOpens X := by
  constructor
  intro U
  change (irreducibleComponents U.toOpens).Finite
  -- Local instance justification (proof-local temporary data): The chosen compact open supplies the compactness witness for its open subscheme.
  letI : CompactSpace U.toOpens := isCompact_iff_compactSpace.mp U.isCompact
  -- Local instance justification (proof-local temporary data): Combining this compactness witness with inherited local Noetherianity supplies the Noetherian structure used by the finite-components theorem.
  letI : IsNoetherian U.toOpens :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := inferInstance }
  exact finite_irreducibleComponents_of_isNoetherian

end HasFiniteIrreducibleComponentsOnCompactOpens

/-- The irreducible components of every quasi-compact open form a finite type
when the ambient scheme has finite components on quasi-compact opens. -/
instance instFiniteIrreducibleComponentsCompactOpens (X : Scheme.{u})
    [HasFiniteIrreducibleComponentsOnCompactOpens X] (U : CompactOpens X) :
    Finite (irreducibleComponents U) :=
  HasFiniteIrreducibleComponentsOnCompactOpens.finite_irreducibleComponents U

/-- The section ring of an affine open has finitely many minimal primes when
the scheme has finitely many irreducible components on compact opens. -/
@[stacks 035P]
theorem affineOpen_sections_finite_minimalPrimes {X : Scheme.{u}}
    [HasFiniteIrreducibleComponentsOnCompactOpens X] (U : X.affineOpens) :
    (minimalPrimes Γ(X, (U : X.Opens))).Finite := by
  let V : CompactOpens X :=
    ⟨⟨(U : Set X), U.2.isCompact⟩, U.1.2⟩
  have hfiniteU : (irreducibleComponents U).Finite := by
    change (irreducibleComponents V).Finite
    exact HasFiniteIrreducibleComponentsOnCompactOpens.finite_irreducibleComponents V
  let f : ↥(U : X.Opens) → PrimeSpectrum Γ(X, (U : X.Opens)) :=
    fun x ↦ U.2.isoSpec.hom.base x
  have hf : IsHomeomorph f := by
    exact (TopCat.isIso_iff_isHomeomorph U.2.isoSpec.hom.base).mp inferInstance
  let componentEquiv :
      irreducibleComponents (PrimeSpectrum Γ(X, (U : X.Opens))) ≃o
        irreducibleComponents U :=
    irreducibleComponentsEquivOfIsPreirreducibleFiber f hf.continuous hf.isOpenMap
      (fun _ ↦ (Set.subsingleton_singleton.preimage hf.injective).isPreirreducible)
      hf.surjective
  let e : minimalPrimes Γ(X, (U : X.Opens)) ≃ irreducibleComponents U :=
    (minimalPrimes.equivIrreducibleComponents Γ(X, (U : X.Opens))).toEquiv.trans
      componentEquiv.toEquiv
  exact @Finite.of_injective _ _ hfiniteU e e.injective

namespace Opens

/-- The generic points of an open subscheme, viewed as points of the ambient scheme. -/
def genericPointsInAmbient {X : Scheme.{u}} (U : X.Opens) : Set X :=
  Subtype.val '' genericPoints U

/-- A dense open subscheme of a scheme with finite irreducible components on
quasi-compact opens has the same generic points as the ambient scheme. -/
theorem genericPointsInAmbient_eq_of_dense {X : Scheme.{u}}
    [HasFiniteIrreducibleComponentsOnCompactOpens X] (U : X.Opens)
    (hU : Dense (U : Set X)) :
    U.genericPointsInAmbient = genericPoints X := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    let z' : ↥(U : Scheme) := ⟨z.1, z.2⟩
    have hz' : z' ∈ genericPoints (U : Scheme) := hz
    let f : ↥(U : Scheme) → X := fun z ↦ U.ι.base z
    have hf : Topology.IsOpenEmbedding f :=
      (inferInstance : IsOpenImmersion U.ι).base_open
    let C : irreducibleComponents X :=
      ⟨irreducibleComponent (f z'), irreducibleComponent_mem_irreducibleComponents (f z')⟩
    have hmeet : ((C : Set X) ∩ Set.range f).Nonempty :=
      ⟨f z', mem_irreducibleComponent, z', rfl⟩
    have hpre : f ⁻¹' (C : Set X) ∈ irreducibleComponents U :=
      preimage_mem_irreducibleComponents C.2 hf hmeet
    have hsub : closure ({z'} : Set ↥(U : Scheme)) ⊆ f ⁻¹' (C : Set X) :=
      closure_minimal (by
        intro y hy
        have hyz : y = z' := by
          exact Set.mem_singleton_iff.mp hy
        subst y
        exact mem_irreducibleComponent)
        ((isClosed_of_mem_irreducibleComponents C.1 C.2).preimage hf.continuous)
    have heq : closure ({z'} : Set ↥(U : Scheme)) = f ⁻¹' (C : Set X) :=
      Set.Subset.antisymm hsub (hz'.2 hpre.1 hsub)
    have hclosure : closure (f '' (f ⁻¹' (C : Set X))) = C :=
      closure_image_preimage_of_isPreirreducible f hf.isOpenMap C.1
        (by exact ⟨z, mem_irreducibleComponent⟩) C.2.1.2
        (isClosed_of_mem_irreducibleComponents C.1 C.2)
    change closure ({f z'} : Set X) ∈ irreducibleComponents X
    convert C.2 using 1
    calc
      closure ({f z'} : Set X) =
          closure (f '' closure ({z'} : Set ↥(U : Scheme))) := by
        rw [closure_image_closure hf.continuous]
        simp
      _ = closure (f '' (f ⁻¹' (C : Set X))) := by rw [heq]
      _ = C := hclosure
  · intro hx
    let η : genericPoints X := ⟨x, hx⟩
    obtain ⟨A, hA, hxA, -⟩ :=
      exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
    let K : CompactOpens X := ⟨⟨(A : Set X), hA.isCompact⟩, A.2⟩
    have hfiniteA : (irreducibleComponents A).Finite := by
      change (irreducibleComponents K).Finite
      exact HasFiniteIrreducibleComponentsOnCompactOpens.finite_irreducibleComponents K
    let fA : ↥(A : Scheme) → X := fun z ↦ A.ι.base z
    have hfA : Topology.IsOpenEmbedding fA :=
      (inferInstance : IsOpenImmersion A.ι).base_open
    let ZA : irreducibleComponents A :=
      ⟨fA ⁻¹' (genericPoints.component η : Set X),
        preimage_mem_irreducibleComponents (genericPoints.component η).2 hfA
          ⟨x, subset_closure (Set.mem_singleton x), ⟨⟨x, hxA⟩, rfl⟩⟩⟩
    let V : Set A := (⋃₀ (irreducibleComponents A \ {(ZA : Set A)}))ᶜ
    have hVopen : IsOpen V := by
      dsimp only [V]
      rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact hfiniteA.sdiff.isClosed_biUnion fun W hW ↦
        isClosed_of_mem_irreducibleComponents W hW.1
    have hVclosure : closure V = (ZA : Set A) :=
      closure_sUnion_irreducibleComponents_sdiff_singleton hfiniteA ZA.1 ZA.2
    have hVnonempty : V.Nonempty := by
      apply Set.Nonempty.of_closure
      rw [hVclosure]
      exact ZA.2.1.nonempty
    have himageOpen : IsOpen (fA '' V) := hfA.isOpenMap V hVopen
    have himageNonempty : (fA '' V).Nonempty := hVnonempty.image fA
    obtain ⟨y, hyImage, hyU⟩ :=
      hU.inter_open_nonempty (fA '' V) himageOpen himageNonempty
    have hyComponent : y ∈ (genericPoints.component η : Set X) := by
      obtain ⟨z, hzV, rfl⟩ := hyImage
      have hzZA : z ∈ (ZA : Set A) := hVclosure ▸ subset_closure hzV
      exact hzZA
    have hxU : x ∈ U :=
      (genericPoints.isGenericPoint η).mem_open_set_iff U.2 |>.2
        ⟨y, hyComponent, hyU⟩
    let z : U := ⟨x, hxU⟩
    let z' : ↥(U : Scheme) := ⟨x, hxU⟩
    refine ⟨z, ?_, rfl⟩
    let f : ↥(U : Scheme) → X := fun z ↦ U.ι.base z
    have hf : Topology.IsOpenEmbedding f :=
      (inferInstance : IsOpenImmersion U.ι).base_open
    have hmeet : ((genericPoints.component η : Set X) ∩ Set.range f).Nonempty :=
      ⟨x, subset_closure (Set.mem_singleton x), ⟨⟨x, hxU⟩, rfl⟩⟩
    have hpre := preimage_mem_irreducibleComponents
      (genericPoints.component η).2 hf hmeet
    change closure ({z'} : Set ↥(U : Scheme)) ∈ irreducibleComponents U
    convert hpre using 1
    change closure ({z'} : Set ↥(U : Scheme)) = f ⁻¹' closure ({x} : Set X)
    rw [hf.isOpenMap.preimage_closure_eq_closure_preimage hf.continuous]
    congr 1
    ext w
    constructor
    · intro hw
      subst w
      rfl
    · intro hw
      apply Subtype.ext
      exact hw

end Opens

end AlgebraicGeometry.Scheme
