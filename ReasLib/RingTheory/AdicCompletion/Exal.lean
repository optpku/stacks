module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.FiniteType
public import ReasLib.RingTheory.AdicCompletion.Exactness.ShortComplex
public import ReasLib.RingTheory.AdicCompletion.FilteredAdditive
public import ReasLib.RingTheory.AdicCompletion.Map
public import ReasLib.RingTheory.Extension.SquareZero
public import Mathlib.RingTheory.Smooth.Locus

/-!
# Adic completion of square-zero algebra extensions

Completion along the inverse-image ideal induces a map on cotangent extension
classes. For a finite type algebra over a field, smooth off the closed subset,
this map is bijective for finite coefficients.
-/

@[expose] public section
noncomputable section
universe u
open Algebra Algebra.Generators Algebra.Extension
open RingHom RingHom.AdicContinuous AdicCompletion CategoryTheory
namespace Algebra.SquareZeroAlgExtension
variable {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

/-- Inverse image of `J` along the projection of a square-zero extension. -/
def adicCompletionIdeal (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
    @Ideal e.carrier e.commRing.toSemiring :=
  -- Local instance justification (proof-local temporary data): unpack bundled `commRing` so `Ideal.comap` on `e.toB` can elaborate.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack bundled `algebra` so `e.toB` elaborates as an algebra homomorphism.
  letI := e.algebra
  Ideal.comap e.toB.toRingHom J

/-- `adicCompletionIdeal` is the preimage of `J` along the projection. -/
theorem adicCompletionIdeal_eq_comap (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
    (adicCompletionIdeal e J : Set e.carrier) = e.toB ⁻¹' (J : Set B) := rfl

/-- Membership in `adicCompletionIdeal e J` is membership of the image in `J`. -/
theorem mem_adicCompletionIdeal (e : SquareZeroAlgExtension A B N) (J : Ideal B)
    {x : e.carrier} :
    x ∈ adicCompletionIdeal e J ↔ e.toB x ∈ J := Iff.rfl

private def adicCompletionProjectionRing (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  AdicCompletion I e.carrier →+* AdicCompletion J B :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  let hcont : e.toB.toRingHom.AdicContinuous I J :=
    ⟨1, by simpa only [pow_one, I, adicCompletionIdeal] using Ideal.map_comap_le (f := e.toB.toRingHom) (K := J)⟩
  hcont.completionMap

private theorem adicCompletion_projection_commutes (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  ∀ a : A, adicCompletionProjectionRing e J (algebraMap A (AdicCompletion I e.carrier) a) =
    algebraMap A (AdicCompletion J B) a := sorry

private def adicCompletionProjection (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  AdicCompletion I e.carrier →ₐ[A] AdicCompletion J B :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  { toRingHom := adicCompletionProjectionRing e J
    commutes' := adicCompletion_projection_commutes e J }

variable [IsNoetherianRing B] [Module.Finite B N]

private theorem adicCompletion_projection_isSquareZero (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  (adicCompletionProjection e J).toRingHom.IsSquareZeroExtension := sorry

private def adicCompletionKernelIncl (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  AdicCompletion I (RingHom.ker e.toB.toRingHom) → AdicCompletion I e.carrier :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  -- Local instance justification (noncanonical choice): the original projection selects the middle-ring action on B.
  letI : Module e.carrier B := Module.compHom B e.toB.toRingHom
  let kerIncl : RingHom.ker e.toB.toRingHom →ₗ[e.carrier] e.carrier :=
    Submodule.subtype (RingHom.ker e.toB.toRingHom)
  let toBLinear : e.carrier →ₗ[e.carrier] B :=
    { toFun := e.toB
      map_add' := map_add e.toB.toRingHom
      map_smul' := fun r x ↦ by
        change e.toB (r * x) = e.toB r * e.toB x
        exact map_mul e.toB r x }
  let S := ShortComplex.moduleCatMk kerIncl toBLinear (by
    ext x
    exact x.2)
  let S' := AdicCompletion.mapShortComplex I S
  S'.f.hom

private theorem adicCompletion_kernelMap_mem (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  ∀ z : AdicCompletion I (RingHom.ker e.toB.toRingHom),
    adicCompletionKernelIncl e J z ∈ RingHom.ker (adicCompletionProjection e J).toRingHom := sorry

private def adicCompletionKernelMap (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  AdicCompletion I (RingHom.ker e.toB.toRingHom) →
    RingHom.ker (adicCompletionProjection e J).toRingHom :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  fun z ↦ ⟨adicCompletionKernelIncl e J z, adicCompletion_kernelMap_mem e J z⟩

private theorem adicCompletion_kernelMap_bijective (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  Function.Bijective (adicCompletionKernelMap e J) := sorry

private theorem adicCompletion_cotangent_filtration (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  ∀ n (x : Ideal.Cotangent (RingHom.ker e.toB.toRingHom)),
    x ∈ (I ^ n • (⊤ : Submodule e.carrier (Ideal.Cotangent (RingHom.ker e.toB.toRingHom)))) →
    x ∈ (J ^ n • (⊤ : Submodule B (Ideal.Cotangent (RingHom.ker e.toB.toRingHom)))) := sorry

private def adicCompletionKernelValue (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  -- Local instance justification (proof-local temporary data): unpack square-zero evidence for the completed projection.
  letI := adicCompletion_projection_isSquareZero e J
  Ideal.Cotangent (RingHom.ker (adicCompletionProjection e J).toRingHom) → AdicCompletion J N :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  -- Local instance justification (proof-local temporary data): unpack square-zero evidence for the completed projection.
  letI := adicCompletion_projection_isSquareZero e J
  fun x ↦
    let xKer := (RingHom.SquareZeroExtension.toCotangentEquiv_source
      (adicCompletionProjection e J).toRingHom).symm x
    let z := (Equiv.ofBijective (adicCompletionKernelMap e J)
      (adicCompletion_kernelMap_bijective e J)).symm xKer
    let zCot := AdicCompletion.map I (Ideal.toCotangent (RingHom.ker e.toB.toRingHom)) z
    let zCotJ := FilteredAdditiveCompletion.map I J
      (AddMonoidHom.id (Ideal.Cotangent (RingHom.ker e.toB.toRingHom)))
      (adicCompletion_cotangent_filtration e J) zCot
    AdicCompletion.map J e.kernelEquiv.toLinearMap zCotJ

private theorem adicCompletion_kernelValue_add (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  -- Local instance justification (proof-local temporary data): unpack square-zero evidence for the completed projection.
  letI := adicCompletion_projection_isSquareZero e J
  ∀ x y, adicCompletionKernelValue e J (x + y) =
    adicCompletionKernelValue e J x + adicCompletionKernelValue e J y := sorry

private theorem adicCompletion_kernelValue_smul (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  -- Local instance justification (proof-local temporary data): unpack square-zero evidence for the completed projection.
  letI := adicCompletion_projection_isSquareZero e J
  ∀ (r : AdicCompletion J B) x, adicCompletionKernelValue e J (r • x) =
    r • adicCompletionKernelValue e J x := sorry

private theorem adicCompletion_kernelValue_bijective (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  -- Local instance justification (proof-local temporary data): unpack square-zero evidence for the completed projection.
  letI := adicCompletion_projection_isSquareZero e J
  Function.Bijective (adicCompletionKernelValue e J) := sorry

/-- Complete the middle ring along the inverse image of an ideal, with its induced kernel identification. -/
def adicCompletion (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
    SquareZeroAlgExtension A (AdicCompletion J B) (AdicCompletion J N) :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I : Ideal e.carrier := adicCompletionIdeal e J
  let hcont : e.toB.toRingHom.AdicContinuous I J :=
    ⟨1, by simpa only [pow_one, I, adicCompletionIdeal] using Ideal.map_comap_le (f := e.toB.toRingHom) (K := J)⟩
  let toB' : AdicCompletion I e.carrier →ₐ[A] AdicCompletion J B :=
    { toRingHom := hcont.completionMap
      commutes' := by exact adicCompletion_projection_commutes e J }
  -- Local instance justification (proof-local temporary data): the induced completed projection is square-zero.
  letI : toB'.toRingHom.IsSquareZeroExtension := by exact adicCompletion_projection_isSquareZero e J
  -- Local instance justification (noncanonical choice): the original projection selects the middle-ring action on B.
  letI : Module e.carrier B := Module.compHom B e.toB.toRingHom
  let kerIncl : RingHom.ker e.toB.toRingHom →ₗ[e.carrier] e.carrier :=
    Submodule.subtype (RingHom.ker e.toB.toRingHom)
  let toBLinear : e.carrier →ₗ[e.carrier] B :=
    { toFun := e.toB
      map_add' := map_add e.toB.toRingHom
      map_smul' := fun r x ↦ by
        change e.toB (r * x) = e.toB r * e.toB x
        exact map_mul e.toB r x }
  let S := ShortComplex.moduleCatMk kerIncl toBLinear (by
    ext x
    exact x.2)
  let S' := AdicCompletion.mapShortComplex I S
  let completedKerIncl : AdicCompletion I (RingHom.ker e.toB.toRingHom) →
      RingHom.ker toB'.toRingHom :=
    fun z ↦ ⟨S'.f.hom z, by exact adicCompletion_kernelMap_mem e J z⟩
  let completedKerEquiv := Equiv.ofBijective completedKerIncl
    (by exact adicCompletion_kernelMap_bijective e J)
  of toB' (LinearEquiv.ofBijective
    { toFun := fun x ↦
        let xKer := (RingHom.SquareZeroExtension.toCotangentEquiv_source toB'.toRingHom).symm x
        let z := completedKerEquiv.symm xKer
        let zCot := AdicCompletion.map I (Ideal.toCotangent (RingHom.ker e.toB.toRingHom)) z
        let zCotJ := FilteredAdditiveCompletion.map I J
          (AddMonoidHom.id (Ideal.Cotangent (RingHom.ker e.toB.toRingHom)))
          (by exact adicCompletion_cotangent_filtration e J) zCot
        AdicCompletion.map J e.kernelEquiv.toLinearMap zCotJ
      map_add' := by exact adicCompletion_kernelValue_add e J
      map_smul' := by exact adicCompletion_kernelValue_smul e J }
    (by exact adicCompletion_kernelValue_bijective e J))

end Algebra.SquareZeroAlgExtension
namespace Algebra.Exal
variable (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

private theorem adicCompletion_respects [IsNoetherianRing B] [Module.Finite B N] (J : Ideal B)
    (f g : (Generators.self A B).toExtension.Cotangent →ₗ[B] N)
    (h : (LinearMap.range
      (LinearMap.lcomp B N (Generators.self A B).toExtension.cotangentComplex)).quotientRel f g) :
    SquareZeroAlgExtension.toClass ((SquareZeroAlgExtension.ofHom f).adicCompletion J) =
      SquareZeroAlgExtension.toClass ((SquareZeroAlgExtension.ofHom g).adicCompletion J) := sorry

/-- Completion of geometric extensions descends to their cotangent cokernel classes. -/
def adicCompletion [IsNoetherianRing B] [Module.Finite B N] (J : Ideal B) :
    Exal A B N → Exal A (AdicCompletion J B) (AdicCompletion J N) :=
  fun x ↦ Quotient.liftOn x
    (fun f ↦ SquareZeroAlgExtension.toClass ((SquareZeroAlgExtension.ofHom f).adicCompletion J))
    (by exact adicCompletion_respects A B N J)

/-- Completing a conormal class gives the class of its completed graph-ideal realization. -/
theorem adicCompletion_mk [IsNoetherianRing B] [Module.Finite B N] (J : Ideal B)
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    adicCompletion A B N J (mk A B N f) =
      SquareZeroAlgExtension.toClass ((SquareZeroAlgExtension.ofHom f).adicCompletion J) := rfl

/-- Quotient representatives and named conormal classes have the same completion. -/
theorem adicCompletion_apply [IsNoetherianRing B] [Module.Finite B N] (J : Ideal B)
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    adicCompletion A B N J (Quotient.mk _ f) = adicCompletion A B N J (mk A B N f) := rfl

/-- The completion of the class of any geometric extension is the class of its completion. -/
theorem adicCompletion_toClass [IsNoetherianRing B] [Module.Finite B N] (J : Ideal B)
    (e : SquareZeroAlgExtension A B N) :
    adicCompletion A B N J e.toClass = (e.adicCompletion J).toClass := sorry

end Algebra.Exal
namespace Algebra.Exal
variable (k B N : Type u) [Field k] [CommRing B] [Algebra k B]
variable [AddCommGroup N] [Module B N]

/-- Completion of extension classes for a finite type algebra over a field. -/
def adicCompletionOfFiniteType [Algebra.FiniteType k B] [Module.Finite B N] (J : Ideal B) :
    Exal k B N → Exal k (AdicCompletion J B) (AdicCompletion J N) :=
  -- Local instance justification (proof-local temporary data): the base field supplies Noetherianity, but is not determined by B.
  letI := Algebra.FiniteType.isNoetherianRing k B
  adicCompletion k B N J

/-- For a finite type algebra over a field, smooth outside the closed subset of an ideal,
completion induces a bijection on square-zero extension classes with finite coefficients. -/
theorem adicCompletion_bijective [Algebra.FiniteType k B] [Module.Finite B N]
    (J : Ideal B) (hsmooth : (PrimeSpectrum.zeroLocus (J : Set B))ᶜ ⊆ smoothLocus k B) :
    Function.Bijective (adicCompletionOfFiniteType k B N J) := sorry

end Algebra.Exal
