module

public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal
public import ReasLib.RingTheory.Polynomial.Local
public import ReasLib.RingTheory.LocalRing.AdjoinRoot

@[expose] public section

universe u v w

open IsLocalRing
open CategoryTheory Limits
open scoped RatFunc

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Helper for Lemma 10.159.1: a partial stage of the source proof consists of a local flat
`R`-algebra whose residue field has already been identified with an intermediate field of `K`. -/
structure ResidueExtensionStage
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (L : IntermediateField (ResidueField R) K) where
  A : Type*
  commRing : CommRing A
  localRing : IsLocalRing A
  algebra : Algebra R A
  localHom : IsLocalHom (algebraMap R A)
  flat : (algebraMap R A).Flat
  map_maximalIdeal : Ideal.map (algebraMap R A) (maximalIdeal R) = maximalIdeal A
  residueEquiv : ResidueField A ≃+* L

attribute [instance] ResidueExtensionStage.commRing
attribute [instance] ResidueExtensionStage.localRing
attribute [instance] ResidueExtensionStage.algebra
attribute [instance] ResidueExtensionStage.localHom

namespace ResidueExtensionStage

variable {K : Type v} [Field K] [Algebra (ResidueField R) K]
variable {L M N : IntermediateField (ResidueField R) K}

/-- Helper for Lemma 10.159.1: the residue-field identification of a stage induces the canonical
map from the stage residue field into the ambient field `K`. -/
noncomputable def residueToAmbient
    (S : ResidueExtensionStage (R := R) K L) :
    ResidueField S.A →+* K :=
  L.val.toRingHom.comp S.residueEquiv.toRingHom

/-- Helper for Lemma 10.159.1: a stage already carries a canonical surjective ring map onto the
intermediate field it realizes. This is the stage-level quotient map needed for the later
direct-limit kernel argument. -/
noncomputable def toIntermediateFieldHom
    (S : ResidueExtensionStage (R := R) K L) :
    S.A →+* L :=
  S.residueEquiv.toRingHom.comp (algebraMap S.A (ResidueField S.A))

/-- Helper for Lemma 10.159.1: the stage map to its intermediate field is surjective because the
residue map is surjective and the chosen residue-field equivalence is bijective. -/
theorem toIntermediateFieldHom_surjective
    (S : ResidueExtensionStage (R := R) K L) :
    Function.Surjective S.toIntermediateFieldHom := sorry
/-- Helper for Lemma 10.159.1: the canonical quotient map from a stage onto its intermediate
field kills exactly the maximal ideal. This is the residue-field kernel computation needed for the
later direct-limit local-ring argument. -/
theorem ker_toIntermediateFieldHom
    (S : ResidueExtensionStage (R := R) K L) :
    RingHom.ker S.toIntermediateFieldHom = maximalIdeal S.A := sorry
/-- Helper for Lemma 10.159.1: the ambient residue-field map of a stage factors through the
canonical quotient map onto the realized intermediate field. -/
noncomputable def toAmbientRingHom
    (S : ResidueExtensionStage (R := R) K L) :
    S.A →+* K :=
  S.residueToAmbient.comp (algebraMap S.A (ResidueField S.A))

/-- Helper for Lemma 10.159.1: the canonical residue-field map of a stage is injective because
it factors through the embedding of the intermediate field into `K`. -/
theorem residueToAmbient_injective
    (S : ResidueExtensionStage (R := R) K L) :
    Function.Injective S.residueToAmbient := sorry
/-- Helper for Lemma 10.159.1: if a transcendental element `α` generates `Lx` over the residue
field of a stage, then `Lx` is canonically the rational function field on `α`. This isolates the
field-theoretic part of the transcendental successor step. -/
noncomputable def ratFunc_algEquiv_of_transcendental_generator
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx) :
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    letI : IsScalarTower (ResidueField S.A) L Lx :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∀ (α : Lx),
      (hgen : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤) →
      (htrans : Transcendental (ResidueField S.A) α) →
      RatFunc (ResidueField S.A) ≃ₐ[ResidueField S.A] Lx :=
  fun α hgen htrans ↦
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    letI : IsScalarTower (ResidueField S.A) L Lx :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let eTop : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) ≃ₐ[ResidueField S.A] Lx :=
      (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
    -- First identify `Lx` with the simple transcendental extension generated by `α`, then
    -- compose with the standard rational-function-field equivalence.
    (RatFunc.algEquivOfTranscendental α htrans).trans eTop

/-- Helper for Lemma 10.159.1: the transcendental generator equivalence sends a constant rational
function to the corresponding scalar in `Lx`. This is the constant-term computation needed when
comparing residue-field maps in the transcendental successor stage. -/
theorem ratFunc_algEquiv_of_transcendental_generator_C
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx) :
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    letI : IsScalarTower (ResidueField S.A) L Lx :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∀ (α : Lx),
      (hgen : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤) →
      (htrans : Transcendental (ResidueField S.A) α) →
      ∀ x : ResidueField S.A,
      ratFunc_algEquiv_of_transcendental_generator (S := S) hLLx α hgen htrans
        (algebraMap (Polynomial (ResidueField S.A)) (RatFunc (ResidueField S.A))
          (Polynomial.C x)) =
        algebraMap (ResidueField S.A) Lx x := sorry
/-- Helper for Lemma 10.159.1: a morphism of stages is an `R`-algebra map compatible with the
chosen embeddings of the stage residue fields into `K`. -/
structure Hom (hLM : L ≤ M)
    (S : ResidueExtensionStage (R := R) K L)
    (T : ResidueExtensionStage (R := R) K M) where
  toAlgHom : S.A →ₐ[R] T.A
  isLocalHom : IsLocalHom toAlgHom.toRingHom
  residue_comm :
      T.residueToAmbient.comp (ResidueField.map toAlgHom.toRingHom) =
        S.residueToAmbient

attribute [instance] ResidueExtensionStage.Hom.isLocalHom

/-- Helper for Lemma 10.159.1: stage morphisms compose by composing the underlying algebra maps,
and the residue-field compatibility squares compose with them. -/
noncomputable def Hom.comp
    {S : ResidueExtensionStage (R := R) K L}
    {T : ResidueExtensionStage (R := R) K M}
    {U : ResidueExtensionStage (R := R) K N}
    {hLM : L ≤ M} {hMN : M ≤ N}
    (f : Hom hLM S T) (g : Hom hMN T U) :
    Hom (hLM.trans hMN) S U where
  toAlgHom := g.toAlgHom.comp f.toAlgHom
  isLocalHom := sorry
  residue_comm := sorry

/-- Helper for Lemma 10.159.1: every stage carries the identity morphism to itself, providing
the base case for later prefix-system transition maps. -/
noncomputable def Hom.id
    (S : ResidueExtensionStage (R := R) K L) :
    Hom (show L ≤ L by exact le_rfl) S S where
  toAlgHom := AlgHom.id R S.A
  isLocalHom := sorry
  residue_comm := sorry

/-- Helper for Lemma 10.159.1: a stage morphism already commutes with the chosen residue-field
equivalences before passing to the ambient field `K`. This is the intrinsic square needed for the
later direct-limit comparison on residue fields. -/
theorem Hom.residueEquiv_comm
    {hLM : L ≤ M}
    {S : ResidueExtensionStage (R := R) K L}
    {T : ResidueExtensionStage (R := R) K M}
    (f : Hom hLM S T) :
    T.residueEquiv.toRingHom.comp (ResidueField.map f.toAlgHom.toRingHom) =
      (IntermediateField.inclusion hLM).toRingHom.comp S.residueEquiv.toRingHom := sorry
/-- Helper for Lemma 10.159.1: stage morphisms commute with the canonical quotient maps onto the
realized intermediate fields. This is the ring-level compatibility needed to pass the stage maps
to the later direct limit. -/
theorem Hom.toIntermediateFieldHom_comm
    {hLM : L ≤ M}
    {S : ResidueExtensionStage (R := R) K L}
    {T : ResidueExtensionStage (R := R) K M}
    (f : Hom hLM S T) :
    T.toIntermediateFieldHom.comp f.toAlgHom.toRingHom =
      (IntermediateField.inclusion hLM).toRingHom.comp S.toIntermediateFieldHom := sorry
/-- Helper for Lemma 10.159.1: the trivial stage at the bottom intermediate field is the original
local ring `R` itself. This is the verified starting point of the transfinite construction. -/
noncomputable def base
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    ResidueExtensionStage (R := R) K (⊥ : IntermediateField (ResidueField R) K) where
  A := R
  commRing := inferInstance
  localRing := inferInstance
  algebra := inferInstance
  localHom := by
    -- The identity map of a local ring is a local ring homomorphism.
    simpa using (inferInstance : IsLocalHom (RingHom.id R))
  flat := by
    -- The identity map is flat.
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  map_maximalIdeal := by
    -- The maximal ideal is unchanged under the identity algebra map.
    simp
  residueEquiv := by
    -- The residue field of the base stage is the bottom intermediate field.
    refine
      { toFun := fun x ↦
          ⟨algebraMap (ResidueField R) K x, by
            rw [IntermediateField.mem_bot]
            exact ⟨x, rfl⟩⟩
        invFun := fun x ↦ IntermediateField.botEquiv (ResidueField R) K x
        left_inv := ?_
        right_inv := ?_
        map_mul' := ?_
        map_add' := ?_ }
    · intro x
      exact IntermediateField.botEquiv_def (F := ResidueField R) (E := K) x
    · intro x
      change (IntermediateField.botEquiv (ResidueField R) K).symm
          (IntermediateField.botEquiv (ResidueField R) K x) = x
      exact (IntermediateField.botEquiv (ResidueField R) K).symm_apply_apply x
    · intro x y
      ext
      simp
    · intro x y
      ext
      simp

/-- Helper for Lemma 10.159.1: the ambient residue-field map of the base stage is the original
scalar map from `ResidueField R` into `K`. -/
theorem base_residueToAmbient_eq_algebraMap
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    (base (R := R) K).residueToAmbient = algebraMap (ResidueField R) K := sorry
/-- Helper for Lemma 10.159.1: after transporting the stage residue-field algebra onto the
one-generator extension `L(x)`, the adjoined element still generates the whole field over the new
base residue field. This isolates the source proof's simple-extension input before the
transcendental/algebraic branch split. -/
theorem stage_adjoin_singleton_top
    (S : ResidueExtensionStage (R := R) K L) (x : K) :
    let Lx : IntermediateField (ResidueField R) K :=
      (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx :=
      (IntermediateField.inclusion
        (show L ≤ Lx by
          intro y hy
          change y ∈ IntermediateField.adjoin L ({x} : Set K)
          simpa using
            (IntermediateField.adjoin.algebraMap_mem (F := L) (S := ({x} : Set K))
              ⟨y, hy⟩))).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    ∃ α : Lx, IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤ := sorry
/-- Helper for Lemma 10.159.1: any local flat extension of a stage whose residue field is already
identified with a larger intermediate field packages into the next source-faithful stage. This
factors the common bookkeeping needed in both the transcendental and algebraic successor steps. -/
theorem of_local_extension
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx)
    (B : Type w) [CommRing B] [IsLocalRing B] [Algebra S.A B] [Algebra R B]
    [IsScalarTower R S.A B] [IsLocalHom (algebraMap S.A B)]
    (hflatB : (algebraMap S.A B).Flat)
    (hmapB : Ideal.map (algebraMap S.A B) (maximalIdeal S.A) = maximalIdeal B)
    (eB : ResidueField B ≃+* Lx)
    (hcompat :
      (Lx.val.toRingHom.comp eB.toRingHom).comp (ResidueField.map (algebraMap S.A B)) =
        S.residueToAmbient) :
    ∃ T : ResidueExtensionStage.{u, v, w} (R := R) K Lx, Nonempty (Hom hLLx S T) := sorry
/-- Helper for Lemma 10.159.1: package an explicit local extension on carrier `B` as the next
stage together with its canonical morphism from the previous stage. This keeps the successor-step
construction on the concrete ring `B` instead of asking elaboration to rediscover that carrier
through an existential witness. -/
theorem stage_and_hom_of_local_extension
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx)
    (B : Type w) [CommRing B] [IsLocalRing B] [Algebra S.A B] [Algebra R B]
    [IsScalarTower R S.A B] [IsLocalHom (algebraMap S.A B)]
    (hflatB : (algebraMap S.A B).Flat)
    (hmapB : Ideal.map (algebraMap S.A B) (maximalIdeal S.A) = maximalIdeal B)
    (eB : ResidueField B ≃+* Lx)
    (hcompat :
      (Lx.val.toRingHom.comp eB.toRingHom).comp (ResidueField.map (algebraMap S.A B)) =
        S.residueToAmbient) :
    ∃ T : ResidueExtensionStage.{u, v, w} (R := R) K Lx,
      Nonempty (Hom hLLx S T) ∧ T.A = B := sorry
/-- Helper for Lemma 10.159.1: after transporting scalars along the residue-field identification
of a stage and then along an inclusion `L ≤ Lx`, the induced map into the ambient field `K` is
still the original residue-field comparison map of the stage. -/
theorem residueToAmbient_comp_algebraMap
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx) :
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    Lx.val.toRingHom.comp (algebraMap (ResidueField S.A) Lx) = S.residueToAmbient := sorry
/-- Helper for Lemma 10.159.1: evaluating the scalar-compatibility identity
`residueToAmbient_comp_algebraMap` on a residue-field element gives the pointwise formula used in
the transcendental successor branch. -/
theorem residueToAmbient_algebraMap_apply
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx) :
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    ∀ x : ResidueField S.A,
      Lx.val.toRingHom (algebraMap (ResidueField S.A) Lx x) = S.residueToAmbient x := sorry
/-- Helper for Lemma 10.159.1: the simple extension `L(x)` always contains the previous stage
field `L` after restricting scalars back to `ResidueField R`. This is the canonical inclusion
used in the source proof's successor step. -/
theorem le_restrictScalars_adjoin_singleton
    (L : IntermediateField (ResidueField R) K) (x : K) :
    L ≤ (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R) := sorry
/-- Helper for Lemma 10.159.1: over a field, the negation of transcendence is exactly
integrality. This is the field-theoretic dichotomy used when the source proof passes from a
simple extension to its transcendental/algebraic cases. -/
theorem isIntegral_of_not_transcendental
    {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
    {x : E} (h : ¬ Transcendental F x) :
    IsIntegral F x := sorry
/-- Helper for Lemma 10.159.1: the simple algebraic generator equivalence respects coefficients
from the base residue field after transporting along the top-field identification. -/
theorem adjoinRootEquivAdjoin_topEquiv_apply_algebraMap
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K}
    [Algebra (ResidueField S.A) L]
    [Algebra L Lx]
    [Algebra (ResidueField S.A) Lx]
    [IsScalarTower (ResidueField S.A) L Lx]
    (α : Lx)
    (hgen : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤)
    (hint : IsIntegral (ResidueField S.A) α)
    (x : ResidueField S.A) :
    let eTop : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) ≃ₐ[ResidueField S.A] Lx :=
      (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
    eTop
        ((IntermediateField.adjoinRootEquivAdjoin (ResidueField S.A) hint)
          (algebraMap (ResidueField S.A) (AdjoinRoot (minpoly (ResidueField S.A) α)) x)) =
      algebraMap (ResidueField S.A) Lx x := sorry
/-- Helper for Lemma 10.159.1: the algebraic `AdjoinRoot` model carries the same map into the
ambient field `K` as the previous stage, once its residue field is identified with the simple
extension generated by `α`. -/
theorem algebraic_local_extension_compat
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K}
    [Algebra (ResidueField S.A) L]
    [Algebra L Lx]
    [Algebra (ResidueField S.A) Lx]
    [IsScalarTower (ResidueField S.A) L Lx]
    (hambient :
      Lx.val.toRingHom.comp (algebraMap (ResidueField S.A) Lx) = S.residueToAmbient)
    (α : Lx)
    (hgen : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤)
    (hint : IsIntegral (ResidueField S.A) α)
    (f : Polynomial S.A)
    (hf : f.Monic)
    (hfmap : Polynomial.Local.reduction f = minpoly (ResidueField S.A) α) :
    letI : IsLocalRing (AdjoinRoot f) :=
      AdjoinRoot.Local.isLocalRing f hf (by simpa [hfmap] using minpoly.irreducible hint)
    letI : IsLocalHom (algebraMap S.A (AdjoinRoot f)) :=
      (AdjoinRoot.Local.mapsMaximalIdeal f
        (by simpa [hfmap] using minpoly.irreducible hint)).isLocalHom
    ∃ eB : ResidueField (AdjoinRoot f) ≃+* Lx,
      (Lx.val.toRingHom.comp eB.toRingHom).comp
          (ResidueField.map (algebraMap S.A (AdjoinRoot f))) =
        S.residueToAmbient := sorry

/-- Helper for Lemma 10.159.1: the canonical transcendental localization over a stage `S`
identifies its residue field with the simple transcendental extension generated by `α`, and this
identification preserves the ambient residue-field map into `K`. -/
theorem transcendental_local_extension_compat_canonical
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx)
    (α : Lx)
    (hgen :
      letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
      letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
      letI : Algebra (ResidueField S.A) Lx :=
        RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
      letI : IsScalarTower (ResidueField S.A) L Lx :=
        IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤)
    (htrans :
      letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
      letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
      letI : Algebra (ResidueField S.A) Lx :=
        RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
      letI : IsScalarTower (ResidueField S.A) L Lx :=
        IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      Transcendental (ResidueField S.A) α) :
    let B : Type _ := Polynomial.Local.atMaximal S.A
    ∃ eB : ResidueField B ≃+* Lx,
      ∀ a : S.A,
        Lx.val.toRingHom (eB (residue B (algebraMap S.A B a))) =
          S.residueToAmbient (residue S.A a) := sorry
/-- Helper for Lemma 10.159.1: a pointwise residue-class computation for a local extension over
`S.A` upgrades to the full residue-field square needed to package the next stage. -/
theorem transcendental_residue_class_bridge
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K}
    (B : Type w) [CommRing B] [IsLocalRing B] [Algebra S.A B] [IsLocalHom (algebraMap S.A B)]
    (eB : ResidueField B ≃+* Lx)
    (hclass :
      ∀ a : S.A,
        Lx.val.toRingHom (eB (residue B (algebraMap S.A B a))) =
          S.residueToAmbient (residue S.A a)) :
    (Lx.val.toRingHom.comp eB.toRingHom).comp (ResidueField.map (algebraMap S.A B)) =
      S.residueToAmbient := sorry
/-- Helper for Lemma 10.159.1: adjoining one element `x : K` to the intermediate field realized
by a stage `S` produces the next source-faithful stage together with its canonical morphism from
`S`. This packages the algebraic/transcendental successor split from the source proof. -/
theorem extend_stage_by_element
    (S : ResidueExtensionStage.{u, v, w} (R := R) K L) (x : K) :
    let Lx : IntermediateField (ResidueField R) K :=
      (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
    ∃ T : ResidueExtensionStage.{u, v, w} (R := R) K Lx,
      Nonempty (Hom (le_restrictScalars_adjoin_singleton (R := R) L x) S T) := sorry
/-- Helper for Lemma 10.159.1: on a top stage, the ambient residue-field map is just the chosen
residue-field equivalence followed by the canonical identification with `K`. -/
theorem top_residueToAmbient_eq
    (T : ResidueExtensionStage (R := R) K (⊤ : IntermediateField (ResidueField R) K)) :
    T.residueToAmbient =
      IntermediateField.topEquiv.toRingHom.comp T.residueEquiv.toRingHom := sorry
end ResidueExtensionStage

end
