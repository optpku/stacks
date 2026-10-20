module

public import ReasLib.LinearAlgebra.QuotientByIdeal.Mapped
public import ReasLib.LinearAlgebra.UniversallyInjective.Quotient
public import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.Injective
public import ReasLib.RingTheory.RingHom.Local.Quotient

/-!
# Flat Cokernels from Closed-Fiber Injectivity

@stack 00ME

This leaf upgrades the closed-fiber injectivity criterion to all finitely
generated ideal quotients.  The resulting universal injectivity makes the
cokernel flat.
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u v w

namespace LinearMap.ClosedFiber

variable {R : Type u} {S : Type v} {M N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing S]
variable [AddCommGroup M] [Module R M] [Module.Flat R M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.Finite S N]

omit [IsLocalRing R] in
/-- Base change of a flat module to `R ⧸ I`, in quotient-module form. -/
theorem flat_quotient (I : Ideal R) :
    Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) := by
  have hTensor : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M) :=
    Module.Flat.baseChange (R := R) (S := R ⧸ I) (M := M)
  let e : (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] M) :=
    (TensorProduct.quotTensorEquivQuotSMul M I).symm.extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  letI : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M) := hTensor
  exact Module.Flat.of_linearEquiv e

/-- Quotienting a module first by `I` and then by the image of `J` agrees
with quotienting directly by `J`. -/
noncomputable def iteratedQuotientEquiv
    {P : Type*} [AddCommGroup P] [Module R P]
    (I J : Ideal R) (hIJ : I ≤ J) :
    ((P ⧸ (I • (⊤ : Submodule R P))) ⧸
      (((Ideal.map (Ideal.Quotient.mk I) J) •
        (⊤ : Submodule (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))))).restrictScalars R))
      ≃ₗ[R] P ⧸ (J • (⊤ : Submodule R P)) := by
  let IM : Submodule R P := I • (⊤ : Submodule R P)
  let JM : Submodule R P := J • (⊤ : Submodule R P)
  let K : Ideal (R ⧸ I) := Ideal.map (Ideal.Quotient.mk I) J
  have hIM_le_JM : IM ≤ JM := by
    dsimp [IM, JM]
    exact Submodule.smul_mono hIJ le_rfl
  have hmap :
      JM.map (Submodule.mkQ IM) =
        ((K • (⊤ : Submodule (R ⧸ I) (P ⧸ IM))).restrictScalars R) := by
    calc
      JM.map (Submodule.mkQ IM) = J • (⊤ : Submodule R (P ⧸ IM)) := by
        simp [JM, IM, Submodule.map_smul'', Submodule.range_mkQ]
      _ = ((Ideal.map (algebraMap R (R ⧸ I)) J) •
          (⊤ : Submodule (R ⧸ I) (P ⧸ IM))).restrictScalars R := by
        symm
        simpa using
          (Ideal.smul_restrictScalars
            (R := R) (S := R ⧸ I) (M := P ⧸ IM) J
            (⊤ : Submodule (R ⧸ I) (P ⧸ IM)))
      _ = ((K • (⊤ : Submodule (R ⧸ I) (P ⧸ IM))).restrictScalars R) := by
        rw [Ideal.Quotient.algebraMap_eq]
  let eDenom :
      ((P ⧸ IM) ⧸
          (((K • (⊤ : Submodule (R ⧸ I) (P ⧸ IM))).restrictScalars R))) ≃ₗ[R]
        ((P ⧸ IM) ⧸ JM.map (Submodule.mkQ IM)) :=
    Submodule.quotEquivOfEq
      (((K • (⊤ : Submodule (R ⧸ I) (P ⧸ IM))).restrictScalars R))
      (JM.map (Submodule.mkQ IM)) hmap.symm
  exact eDenom.trans (Submodule.quotientQuotientEquivQuotient IM JM hIM_le_JM)

omit [IsLocalRing R] in
/-- `iteratedQuotientEquiv` fixes double quotient representatives. -/
@[simp]
theorem iteratedQuotientEquiv_mk_mk
    {P : Type*} [AddCommGroup P] [Module R P]
    (I J : Ideal R) (hIJ : I ≤ J) (x : P) :
    iteratedQuotientEquiv (P := P) I J hIJ
      (Submodule.Quotient.mk (Submodule.Quotient.mk x)) =
        Submodule.Quotient.mk x := by
  dsimp [iteratedQuotientEquiv]
  rfl

omit [Module.Flat R M] in
/-- Naturality of the iterated-quotient comparison for a linear map. -/
theorem iteratedQuotient_naturality
    (f : N →ₗ[R] M) {I : Ideal R} (hI : I ≤ maximalIdeal R) :
    let K : Ideal (R ⧸ I) :=
      Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R)
    let eN := iteratedQuotientEquiv (P := N) I (maximalIdeal R) hI
    let eM := iteratedQuotientEquiv (P := M) I (maximalIdeal R) hI
    eM.toLinearMap.comp (((f.reduceModIdeal I).reduceModIdeal K).restrictScalars R) =
      (f.quotientMapByIdeal (maximalIdeal R)).comp eN.toLinearMap := by
  dsimp
  apply DFunLike.ext
  intro z
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
    ((((Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R)) •
      (⊤ : Submodule (R ⧸ I) (N ⧸ (I • (⊤ : Submodule R N))))).restrictScalars R)) z
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R N)) y
  change
    (iteratedQuotientEquiv (P := M) I (maximalIdeal R) hI).toLinearMap
        ((((f.reduceModIdeal I).reduceModIdeal
          (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R))).restrictScalars R)
          (Submodule.Quotient.mk (Submodule.Quotient.mk x))) =
      ((f.quotientMapByIdeal (maximalIdeal R)).comp
        (iteratedQuotientEquiv (P := N) I (maximalIdeal R) hI).toLinearMap)
        (Submodule.Quotient.mk (Submodule.Quotient.mk x))
  calc
    (iteratedQuotientEquiv (P := M) I (maximalIdeal R) hI).toLinearMap
        ((((f.reduceModIdeal I).reduceModIdeal
          (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R))).restrictScalars R)
          (Submodule.Quotient.mk (Submodule.Quotient.mk x))) =
        (iteratedQuotientEquiv (P := M) I (maximalIdeal R) hI).toLinearMap
          (Submodule.Quotient.mk (Submodule.Quotient.mk (f x))) := by rfl
    _ = Submodule.Quotient.mk (f x) := by simp
    _ = (f.quotientMapByIdeal (maximalIdeal R))
          ((iteratedQuotientEquiv (P := N) I (maximalIdeal R) hI).toLinearMap
            (Submodule.Quotient.mk (Submodule.Quotient.mk x))) := by simp
    _ = ((f.quotientMapByIdeal (maximalIdeal R)).comp
          (iteratedQuotientEquiv (P := N) I (maximalIdeal R) hI).toLinearMap)
          (Submodule.Quotient.mk (Submodule.Quotient.mk x)) := by rfl

omit [Module.Flat R M] in
/-- Closed-fiber injectivity descends to the double reduction associated to
every proper ideal. -/
theorem quotient_local_closedFiber_injective
    (f : N →ₗ[R] M) {I : Ideal R} (htop : I ≠ ⊤)
    (hf : Function.Injective (f.quotientMapByIdeal (maximalIdeal R))) :
    Function.Injective ((((f.reduceModIdeal I).reduceModIdeal
      (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R))).restrictScalars R)) := by
  let K : Ideal (R ⧸ I) := Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R)
  have hI : I ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal htop
  let eN := iteratedQuotientEquiv (P := N) I (maximalIdeal R) hI
  let eM := iteratedQuotientEquiv (P := M) I (maximalIdeal R) hI
  have hcompare :
      ((((f.reduceModIdeal I).reduceModIdeal K).restrictScalars R)).comp
          eN.symm.toLinearMap =
        eM.symm.toLinearMap.comp (f.quotientMapByIdeal (maximalIdeal R)) := by
    apply DFunLike.ext
    intro x
    have hx :
        eM ((((f.reduceModIdeal I).reduceModIdeal K).restrictScalars R) (eN.symm x)) =
          ((f.quotientMapByIdeal (maximalIdeal R)).comp eN.toLinearMap) (eN.symm x) :=
      LinearMap.congr_fun (iteratedQuotient_naturality (f := f) (I := I) hI) (eN.symm x)
    apply eM.injective
    calc
      eM ((((f.reduceModIdeal I).reduceModIdeal K).restrictScalars R) (eN.symm x)) =
          ((f.quotientMapByIdeal (maximalIdeal R)).comp eN.toLinearMap) (eN.symm x) := hx
      _ = (f.quotientMapByIdeal (maximalIdeal R)) x := by simp [LinearMap.comp_apply]
      _ = eM (eM.symm ((f.quotientMapByIdeal (maximalIdeal R)) x)) := by simp
  exact LinearMap.injective_of_ladder_linearEquiv (R := R) hcompare hf

/-- The quotient by the extended ideal action and the quotient by the source
ideal action are canonically equivalent over `R ⧸ I`. -/
noncomputable def quotientSourceEquiv (I : Ideal R) :
    (N ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S N))) ≃ₗ[R ⧸ I]
      N ⧸ (I • (⊤ : Submodule R N)) :=
  Ideal.Quotient.Map.smulTopQuotientEquivQuotient
    (R := R) (S := S) (M := N) I

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [IsNoetherianRing S] [Module.Finite S N] in
/-- `quotientSourceEquiv` fixes quotient representatives. -/
@[simp]
theorem quotientSourceEquiv_mk (I : Ideal R) (x : N) :
    quotientSourceEquiv (R := R) (S := S) (N := N) I
      (Submodule.Quotient.mk x) = Submodule.Quotient.mk x :=
  Ideal.Quotient.Map.smulTopQuotientEquivQuotient_apply_mk
    (R := R) (S := S) (M := N) I x

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [IsNoetherianRing S] [Module.Finite S N] in
/-- The inverse `quotientSourceEquiv` also fixes quotient representatives. -/
@[simp]
theorem quotientSourceEquiv_symm_mk (I : Ideal R) (x : N) :
    (quotientSourceEquiv (R := R) (S := S) (N := N) I).symm
      (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
  apply (quotientSourceEquiv (R := R) (S := S) (N := N) I).injective
  simp

/-- The quotient-source comparison induces an equivalence on the closed
fibers over a proper quotient local ring. -/
noncomputable def quotientSourceClosedFiberEquiv
    (I : Ideal R) [IsLocalRing (R ⧸ I)] :
    ((N ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S N))) ⧸
      ((maximalIdeal (R ⧸ I)) •
        (⊤ : Submodule (R ⧸ I)
          (N ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S N)))))) ≃ₗ[R ⧸ I]
      ((N ⧸ (I • (⊤ : Submodule R N))) ⧸
        ((maximalIdeal (R ⧸ I)) •
          (⊤ : Submodule (R ⧸ I) (N ⧸ (I • (⊤ : Submodule R N)))))) := by
  let e := quotientSourceEquiv (R := R) (S := S) (N := N) I
  let Psrc : Submodule (R ⧸ I)
      (N ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S N))) :=
    (maximalIdeal (R ⧸ I)) •
      (⊤ : Submodule (R ⧸ I)
        (N ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S N))))
  let Ptgt : Submodule (R ⧸ I) (N ⧸ (I • (⊤ : Submodule R N))) :=
    (maximalIdeal (R ⧸ I)) •
      (⊤ : Submodule (R ⧸ I) (N ⧸ (I • (⊤ : Submodule R N))))
  have hmap : Psrc.map e.toLinearMap = Ptgt := by
    simp [Psrc, Ptgt, Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  exact Submodule.Quotient.equiv Psrc Ptgt e hmap

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [IsNoetherianRing S] [Module.Finite S N] in
/-- The induced closed-fiber comparison fixes double quotient
representatives. -/
@[simp]
theorem quotientSourceClosedFiberEquiv_mk_mk
    (I : Ideal R) [IsLocalRing (R ⧸ I)] (x : N) :
    quotientSourceClosedFiberEquiv (R := R) (S := S) (N := N) I
      (Submodule.Quotient.mk (Submodule.Quotient.mk x)) =
        Submodule.Quotient.mk (Submodule.Quotient.mk x) := by
  dsimp [quotientSourceClosedFiberEquiv]
  simp

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [IsNoetherianRing S] [Module.Finite S N] in
/-- The inverse induced closed-fiber comparison also fixes double quotient
representatives. -/
@[simp]
theorem quotientSourceClosedFiberEquiv_symm_mk_mk
    (I : Ideal R) [IsLocalRing (R ⧸ I)] (x : N) :
    (quotientSourceClosedFiberEquiv (R := R) (S := S) (N := N) I).symm
      (Submodule.Quotient.mk (Submodule.Quotient.mk x)) =
        Submodule.Quotient.mk (Submodule.Quotient.mk x) := by
  apply (quotientSourceClosedFiberEquiv (R := R) (S := S) (N := N) I).injective
  simp

omit [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
  [Module.Flat R M] [Module.Finite S N] in
/-- The map from the extended-ideal quotient has injective closed fiber over
every proper quotient `R ⧸ I`. -/
theorem quotientSource_mod_maximalIdeal_injective
    (f : N →ₗ[R] M) {I : Ideal R} (htop : I ≠ ⊤)
    (hf : Function.Injective (f.quotientMapByIdeal (maximalIdeal R))) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let Q : Type u := R ⧸ I
    let e := quotientSourceEquiv (R := R) (S := S) (N := N) I
    let g : (N ⧸ (J • (⊤ : Submodule S N))) →ₗ[Q]
        (M ⧸ (I • (⊤ : Submodule R M))) :=
      (f.reduceModIdeal I).comp e.toLinearMap
    Function.Injective (g.quotientMapByIdeal
      (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R))) := by
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let Q : Type u := R ⧸ I
  let T : Type v := S ⧸ J
  letI : IsLocalRing Q := IsLocalRing.quotient I htop
  letI : Algebra Q T :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (R := R) (A := S) (p := I) (P := J) Ideal.le_comap_map
  let e := quotientSourceEquiv (R := R) (S := S) (N := N) I
  let eClosed := quotientSourceClosedFiberEquiv (R := R) (S := S) (N := N) I
  let g : (N ⧸ (J • (⊤ : Submodule S N))) →ₗ[Q]
      (M ⧸ (I • (⊤ : Submodule R M))) :=
    (f.reduceModIdeal I).comp e.toLinearMap
  change Function.Injective
    (g.quotientMapByIdeal (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R)))
  have hmax :
      Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal Q :=
    IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  rw [hmax]
  have hf_closed :
      Function.Injective ((f.reduceModIdeal I).quotientMapByIdeal (maximalIdeal Q)) := by
    rw [← hmax]
    simpa [LinearMap.quotientMapByIdeal_eq_reduceModIdeal_restrictScalars
      (R := Q) (f.reduceModIdeal I)
        (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R))] using
      (quotient_local_closedFiber_injective
        (R := R) (M := M) (N := N) f (I := I) htop hf)
  let eTarget :
      ((M ⧸ (I • (⊤ : Submodule R M))) ⧸
        ((maximalIdeal Q) •
          (⊤ : Submodule Q (M ⧸ (I • (⊤ : Submodule R M)))))) ≃ₗ[Q]
        ((M ⧸ (I • (⊤ : Submodule R M))) ⧸
          ((maximalIdeal Q) •
            (⊤ : Submodule Q (M ⧸ (I • (⊤ : Submodule R M)))))) :=
    LinearEquiv.refl Q _
  have hcompare :
      (g.quotientMapByIdeal (maximalIdeal Q)).comp eClosed.symm.toLinearMap =
        eTarget.toLinearMap.comp
          ((f.reduceModIdeal I).quotientMapByIdeal (maximalIdeal Q)) := by
    apply DFunLike.ext
    intro z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
      ((maximalIdeal Q) •
        (⊤ : Submodule Q (N ⧸ (I • (⊤ : Submodule R N))))) z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R N)) y
    change
      (g.quotientMapByIdeal (maximalIdeal Q))
        ((quotientSourceClosedFiberEquiv (R := R) (S := S) (N := N) I).symm
          (Submodule.Quotient.mk (Submodule.Quotient.mk x))) =
        (eTarget.toLinearMap.comp
          ((f.reduceModIdeal I).quotientMapByIdeal (maximalIdeal Q)))
          (Submodule.Quotient.mk (Submodule.Quotient.mk x))
    rw [quotientSourceClosedFiberEquiv_symm_mk_mk]
    change
      Submodule.Quotient.mk (g (Submodule.Quotient.mk x)) =
        (eTarget.toLinearMap.comp
          ((f.reduceModIdeal I).quotientMapByIdeal (maximalIdeal Q)))
          (Submodule.Quotient.mk (Submodule.Quotient.mk x))
    change
      Submodule.Quotient.mk
          ((f.reduceModIdeal I)
            (quotientSourceEquiv (R := R) (S := S) (N := N) I
              (Submodule.Quotient.mk x))) =
        (eTarget.toLinearMap.comp
          ((f.reduceModIdeal I).quotientMapByIdeal (maximalIdeal Q)))
          (Submodule.Quotient.mk (Submodule.Quotient.mk x))
    rw [quotientSourceEquiv_mk]
    rfl
  exact LinearMap.injective_of_ladder_linearEquiv (R := Q) hcompare hf_closed

include S

/-- Closed-fiber injectivity makes the reduction of the map modulo every
proper ideal injective. -/
theorem reduceModIdeal_injective
    (f : N →ₗ[R] M) {I : Ideal R} (htop : I ≠ ⊤)
    (hf : Function.Injective (f.quotientMapByIdeal (maximalIdeal R))) :
    Function.Injective (f.reduceModIdeal I) := by
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let Q : Type u := R ⧸ I
  let T : Type v := S ⧸ J
  letI : IsLocalRing Q := IsLocalRing.quotient I htop
  have hI_le : I ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal htop
  have hJ_lt_top : J < ⊤ :=
    lt_of_le_of_lt (Ideal.map_mono hI_le)
      (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S))
  letI : IsLocalRing T := IsLocalRing.quotient J hJ_lt_top.ne
  letI : IsNoetherianRing T :=
    isNoetherianRing_of_surjective S T
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  letI : Algebra Q T :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (R := R) (A := S) (p := I) (P := J) Ideal.le_comap_map
  letI : IsLocalHom (algebraMap Q T) := by
    change IsLocalHom
      (Ideal.quotientMap J (algebraMap R S) Ideal.le_comap_map)
    exact IsLocalHom.quotient Ideal.le_comap_map hJ_lt_top.ne
  let e := quotientSourceEquiv (R := R) (S := S) (N := N) I
  let g : (N ⧸ (J • (⊤ : Submodule S N))) →ₗ[Q]
      (M ⧸ (I • (⊤ : Submodule R M))) :=
    (f.reduceModIdeal I).comp e.toLinearMap
  have hmax :
      Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal Q :=
    IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hg_closed :
      Function.Injective (g.quotientMapByIdeal (maximalIdeal Q)) := by
    rw [← hmax]
    exact quotientSource_mod_maximalIdeal_injective
      (R := R) (S := S) (M := M) (N := N) f (I := I) htop hf
  letI : Module.Flat Q (M ⧸ (I • (⊤ : Submodule R M))) :=
    flat_quotient (R := R) (M := M) I
  letI : Module.Finite S (N ⧸ (J • (⊤ : Submodule S N))) := by infer_instance
  letI : Module.Finite T (N ⧸ (J • (⊤ : Submodule S N))) :=
    Module.Finite.of_restrictScalars_finite S T
      (N ⧸ (J • (⊤ : Submodule S N)))
  letI : IsScalarTower Q T (N ⧸ (J • (⊤ : Submodule S N))) :=
    IsScalarTower.of_compHom Q T (N ⧸ (J • (⊤ : Submodule S N)))
  have hg : Function.Injective g :=
    LinearMap.ClosedFiber.injective_of_mod_maximalIdeal_injective
      (R := Q) (S := T)
      (M := M ⧸ (I • (⊤ : Submodule R M)))
      (N := N ⧸ (J • (⊤ : Submodule S N))) g hg_closed
  intro x y hxy
  exact e.symm.injective <| hg <| by simp [g, hxy]

/-- Closed-fiber injectivity implies injectivity after quotienting by every
finitely generated ideal. -/
theorem quotientMapByIdeal_injective
    (f : N →ₗ[R] M)
    (hf : Function.Injective (f.quotientMapByIdeal (maximalIdeal R))) :
    ∀ I : Ideal R, I.FG → Function.Injective (f.quotientMapByIdeal I) := by
  intro I _
  by_cases htop : I = ⊤
  · subst I
    intro x y _
    obtain ⟨x', rfl⟩ := Submodule.mkQ_surjective (⊤ • (⊤ : Submodule R N)) x
    obtain ⟨y', rfl⟩ := Submodule.mkQ_surjective (⊤ • (⊤ : Submodule R N)) y
    exact (Submodule.Quotient.eq (⊤ • (⊤ : Submodule R N))).2 (by simp)
  · have hreduce : Function.Injective (f.reduceModIdeal I) :=
      reduceModIdeal_injective
        (R := R) (S := S) (M := M) (N := N) f htop hf
    simpa [LinearMap.quotientMapByIdeal_eq_reduceModIdeal_restrictScalars
      (R := R) f I] using hreduce

/-- The cokernel of a closed-fiber-injective map from a finite module into a
flat module is flat. -/
@[stacks 00ME "closed-fiber flat-cokernel criterion"]
theorem flat_quotient_range_of_mod_maximalIdeal_injective
    (f : N →ₗ[R] M)
    (hf : Function.Injective (f.quotientMapByIdeal (maximalIdeal R))) :
    Module.Flat R (M ⧸ LinearMap.range f) := by
  have hfg : ∀ I : Ideal R, I.FG →
      Function.Injective (f.quotientMapByIdeal I) :=
    quotientMapByIdeal_injective
      (R := R) (S := S) (M := M) (N := N) f hf
  have hUniv : LinearMap.UniversallyInjective.{u, w, w, max u w} f :=
    (LinearMap.universallyInjective_iff_injective_mod_finite_ideal
      (R := R) (M := N) (M' := M) f).2 hfg
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (f₁ := f) (f₂ := (LinearMap.range f).mkQ)
    (g₁ := I.subtype) (g₂ := Submodule.mkQ I)
    f.exact_map_mkQ_range (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective _)
    (hUniv.rTensor_injective (R ⧸ I))
    (Module.Flat.lTensor_preserves_injective_linearMap I.subtype Subtype.val_injective)

end LinearMap.ClosedFiber
