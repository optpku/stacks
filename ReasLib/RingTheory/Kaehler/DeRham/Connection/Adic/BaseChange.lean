/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope.Smooth
public import ReasLib.RingTheory.DividedPowers.Envelope.Coordinates
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.AdicCompletion.Comparison
public import ReasLib.RingTheory.Kaehler.DeRham.Connection.Adic.QuasiNilpotent
public import Mathlib.LinearAlgebra.TensorProduct.Tower

@[expose] public section

noncomputable section

set_option backward.privateInPublic true

open CategoryTheory KaehlerDifferential.DeRham DPPolynomial.DeRham
open scoped TensorProduct

universe u

namespace Connection.Adic

section DifferentialMaps

variable {A D D' : Type u} [CommRing A] [CommRing D] [CommRing D']
variable (fD : A →+* D) (fD' : A →+* D')
variable {JD : Ideal D} {JD' : Ideal D'} (γD : DividedPowers JD) (γD' : DividedPowers JD')
variable (φ : D →+* D') (hA : φ.comp fD = fD') (hDP : γD.IsDPMorphism γD' φ)

/-- The Kähler comparison followed by the target divided-power quotient, with scalars restricted along the given homomorphism. -/
private def formsKaehlerMap :
    -- Local instance justification (noncanonical choice): relative Kähler differentials use the specified source base map.
    letI := fD.toAlgebra
    KaehlerDifferential A D →ₗ[D]
      (ModuleCat.restrictScalars φ).obj (ModuleCat.of D' (dividedPowerDifferential fD' γD')) :=
  -- Local instance justification (noncanonical choice): relative Kähler differentials use the specified source base map.
  letI := fD.toAlgebra
  -- Local instance justification (noncanonical choice): relative Kähler differentials use the specified target base map.
  letI := fD'.toAlgebra
  -- Local instance justification (noncanonical choice): the specified comparison homomorphism selects the source action on the target ring.
  letI := φ.toAlgebra
  -- Local instance justification (defeq pin): the Kähler comparison requires the tower determined by the base-map compatibility equation.
  letI : IsScalarTower A D D' := IsScalarTower.of_algebraMap_eq' hA.symm
  let native := KaehlerDifferential.map A A D D'
  let quotient := (dividedPowerRelations fD' γD').mkQ
  { toFun := fun ω ↦ quotient (native ω)
    map_add' := fun x y ↦ (congrArg quotient (native.map_add x y)).trans (quotient.map_add _ _)
    map_smul' := fun r ω ↦ (congrArg quotient (native.map_smul r ω)).trans (quotient.map_smul _ _) }

include hDP in
/-- A divided-power homomorphism carries every defining differential relation to zero. -/
theorem formsMap_relations :
    -- Local instance justification (noncanonical choice): the relation submodule is relative to the specified source base map.
    letI := fD.toAlgebra
    dividedPowerRelations fD γD ≤ LinearMap.ker (formsKaehlerMap fD fD' γD' φ hA) := sorry

/-- The differential homomorphism induced by a compatible divided-power ring homomorphism. -/
def formsMap : dividedPowerDifferential fD γD →ₗ[D]
    (ModuleCat.restrictScalars φ).obj (ModuleCat.of D' (dividedPowerDifferential fD' γD')) :=
  (dividedPowerRelations fD γD).liftQ (formsKaehlerMap fD fD' γD' φ hA)
    (formsMap_relations fD fD' γD γD' φ hA hDP)

/-- The principal-adic completion of the differential homomorphism induced by a divided-power homomorphism. -/
def completedFormsMap (p : ℕ) :
    AdicCompletion (Ideal.span {(p : D)}) (dividedPowerDifferential fD γD) →+
      AdicCompletion (Ideal.span {(p : D')}) (dividedPowerDifferential fD' γD') :=
  AdicCompletion.completeAddMap D D' p (formsMap fD fD' γD γD' φ hA hDP).toAddMonoidHom

/-- Completed differential functoriality is semilinear over the given coefficient homomorphism. -/
theorem completedFormsMap_smul (p : ℕ) (r : D)
    (ω : AdicCompletion (Ideal.span {(p : D)}) (dividedPowerDifferential fD γD)) :
    completedFormsMap fD fD' γD γD' φ hA hDP p (r • ω) =
      φ r • completedFormsMap fD fD' γD γD' φ hA hDP p ω := sorry

/-- The completed differential homomorphism intertwines the universal derivatives of coefficients. -/
theorem completedFormsMap_derivation (p : ℕ) (r : D) :
    completedFormsMap fD fD' γD γD' φ hA hDP p
        (AdicCompletion.of (Ideal.span {(p : D)}) _ (dividedPowerDifferentialDerivation fD γD r)) =
      AdicCompletion.of (Ideal.span {(p : D')}) _ (dividedPowerDifferentialDerivation fD' γD' (φ r)) := sorry

/-- Completed differential homomorphisms compose with the underlying divided-power homomorphisms. -/
theorem completedFormsMap_comp
    {D'' : Type u} [CommRing D''] (fD'' : A →+* D'')
    {JD'' : Ideal D''} (γD'' : DividedPowers JD'')
    (ψ : D' →+* D'') (hA' : ψ.comp fD' = fD'') (hDP' : γD'.IsDPMorphism γD'' ψ)
    (hcomp : (ψ.comp φ).comp fD = fD'') (hDPcomp : γD.IsDPMorphism γD'' (ψ.comp φ)) (p : ℕ) :
    (completedFormsMap fD' fD'' γD' γD'' ψ hA' hDP' p).comp
        (completedFormsMap fD fD' γD γD' φ hA hDP p) =
      completedFormsMap fD fD'' γD γD'' (ψ.comp φ) hcomp hDPcomp p := sorry

/-- The completed differential homomorphism bundled after restriction of scalars. -/
def completedFormsMapLinear (p : ℕ) :
    AdicCompletion (Ideal.span {(p : D)}) (dividedPowerDifferential fD γD) →ₗ[D]
      (ModuleCat.restrictScalars φ).obj
        (ModuleCat.of D' (AdicCompletion (Ideal.span {(p : D')}) (dividedPowerDifferential fD' γD'))) :=
  { __ := completedFormsMap fD fD' γD γD' φ hA hDP p
    map_smul' := completedFormsMap_smul fD fD' γD γD' φ hA hDP p }

end DifferentialMaps

section ScalarExtension

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- The scalar action selected by a specified extension homomorphism. -/
@[implicit_reducible] def scalarExtensionAlgebra : Algebra R S := f.toAlgebra

/-- Extension of scalars of a bundled module along a specified ring homomorphism. -/
def scalarExtensionTensor (M : ModuleCat.{u} R) : ModuleCat.{u} S :=
  (ModuleCat.extendScalars f).obj M

/-- The principal-adic completed extension of scalars. -/
def completedScalarExtension (p : ℕ) (M : ModuleCat.{u} R) : ModuleCat.{u} S :=
  ModuleCat.of S (AdicCompletion (Ideal.span {(p : S)}) (scalarExtensionTensor f M))

/-- A linear coefficient homomorphism induces the tensor-product extension homomorphism. -/
def scalarExtensionTensorMap {M N : ModuleCat.{u} R} (g : M ⟶ N) :
    scalarExtensionTensor f M ⟶ scalarExtensionTensor f N :=
  (ModuleCat.extendScalars f).map g

/-- Completion of the tensor-product extension homomorphism. -/
def completedScalarExtensionMap (p : ℕ) {M N : ModuleCat.{u} R} (g : M ⟶ N) :
    completedScalarExtension f p M ⟶ completedScalarExtension f p N :=
  ModuleCat.ofHom (AdicCompletion.map (Ideal.span {(p : S)}) (scalarExtensionTensorMap f g).hom)

/-- Completed scalar extension preserves identity and composite coefficient homomorphisms. -/
theorem completedScalarExtensionMap_laws (p : ℕ) :
    (∀ M : ModuleCat.{u} R, completedScalarExtensionMap f p (𝟙 M) = 𝟙 _) ∧
      (∀ {M N P : ModuleCat.{u} R} (g : M ⟶ N) (h : N ⟶ P),
        completedScalarExtensionMap f p (g ≫ h) =
          completedScalarExtensionMap f p g ≫ completedScalarExtensionMap f p h) := sorry

end ScalarExtension

section Connections

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable (fB : A →+* B) (fC : A →+* C)
variable {JB : Ideal B} {JC : Ideal C} (δ : DividedPowers JB) (ε : DividedPowers JC)
variable (p : ℕ) [Fact p.Prime] [Algebra (Int.LocalizationAtPrime p) A]
variable (hB : IsNilpotent (p : B ⧸ JB)) (hC : IsNilpotent (p : C ⧸ JC))
variable (δhat : DividedPowers (Ideal.map (algebraMap B (completedRingB B p)) JB))
variable (εhat : DividedPowers (Ideal.map (algebraMap C (completedRingB C p)) JC))
variable (hδhat : δ.IsDPMorphism δhat (algebraMap B (completedRingB B p)))
variable (hεhat : ε.IsDPMorphism εhat (algebraMap C (completedRingB C p)))
variable (φ : completedRingB B p →+* completedRingB C p)
variable (hA : φ.comp ((algebraMap B (completedRingB B p)).comp fB) =
  (algebraMap C (completedRingB C p)).comp fC)
variable (hDP : δhat.IsDPMorphism εhat φ)

/-- The completed differential comparison with a specified compatible image-ideal extension. -/
private def imageFormsEquiv :=
  DividedPowerDifferential.completedFormsEquivOfImageExtension fB δ p hB
    (DividedPowers.PrincipalCompletion.stableOffset p hB)
    (DividedPowers.PrincipalCompletion.stableOffset_pow_le δ p hB) δhat hδhat

/-- Differential functoriality expressed on the completed forms of the original rings. -/
private def originalFormsMap :
    DividedPowerDifferential.originalCompletion fB δ p →ₛₗ[φ]
      DividedPowerDifferential.originalCompletion fC ε p :=
  let source := imageFormsEquiv fB δ p hB δhat hδhat
  let target := imageFormsEquiv fC ε p hC εhat hεhat
  let map :
      AdicCompletion (Ideal.span {(p : completedRingB B p)})
          (dividedPowerDifferential ((algebraMap B (completedRingB B p)).comp fB) δhat) →ₛₗ[φ]
        AdicCompletion (Ideal.span {(p : completedRingB C p)})
          (dividedPowerDifferential ((algebraMap C (completedRingB C p)).comp fC) εhat) :=
    { __ := completedFormsMap _ _ δhat εhat φ hA hDP p
      map_smul' := completedFormsMap_smul _ _ δhat εhat φ hA hDP p }
  target.symm.toLinearMap.comp (map.comp source.toLinearMap)

/-- Inclusion of coefficients in the tensor-product extension as a semilinear homomorphism. -/
private def coefficientInclude (M : ModuleCat.{u} (completedRingB B p)) :
    M →ₛₗ[φ] scalarExtensionTensor φ M :=
  let unit := ((ModuleCat.extendRestrictScalarsAdj φ).unit.app M).hom
  { __ := unit.toAddMonoidHom
    map_smul' := unit.map_smul }

/-- Inclusion of coefficients in the completed extension as a semilinear homomorphism. -/
private def completedCoefficientInclude (M : ModuleCat.{u} (completedRingB B p)) :
    M →ₛₗ[φ] completedScalarExtension φ p M :=
  (AdicCompletion.of (Ideal.span {(p : completedRingB C p)})
    (scalarExtensionTensor φ M)).comp (coefficientInclude p φ M)

/-- The induced additive homomorphism on completed tensors with one-forms. -/
private def connectionTensorMap (M : ModuleCat.{u} (completedRingB B p)) :
    completedTensorB (completedRingB B p) p M (DividedPowerDifferential.originalCompletion fB δ p) →+
      completedTensorB (completedRingB C p) p (completedScalarExtension φ p M)
        (DividedPowerDifferential.originalCompletion fC ε p) :=
  AdicCompletion.completeAddMap (completedRingB B p) (completedRingB C p) p
    (TensorProduct.map (completedCoefficientInclude p φ M)
      (originalFormsMap fB fC δ ε p hB hC δhat εhat hδhat hεhat φ hA hDP)).toAddMonoidHom

variable (M : ModuleCat.{u} (completedRingB B p))

/-- The tensor Leibniz value for completed scalar extension, without choosing algebraic connection values. -/
private def scalarExtensionValue
    (conn :
      -- Local instance justification (noncanonical choice): the connection is relative to the specified source coefficient homomorphism.
      letI := fB.toAlgebra
      Adic A B δ p M)
    (scalar : completedRingB C p) (m : M) :
    completedTensorB (completedRingB C p) p (completedScalarExtension φ p M)
      (DividedPowerDifferential.originalCompletion fC ε p) :=
  -- Local instance justification (noncanonical choice): projecting the source connection uses its specified base homomorphism.
  letI := fB.toAlgebra
  scalar • connectionTensorMap fB fC δ ε p hB hC δhat εhat hδhat hεhat φ hA hDP M
      (conn.toAddMonoidHom m) +
    AdicCompletion.of (Ideal.span {(p : completedRingB C p)}) _
      (completedCoefficientInclude p φ M m ⊗ₜ[completedRingB C p]
        AdicCompletion.completeAddMap C C p (dividedPowerDifferentialDerivation fC ε).toAddMonoidHom scalar)

variable (conn :
  -- Local instance justification (noncanonical choice): the connection is relative to the specified source coefficient homomorphism.
  letI := fB.toAlgebra
  Adic A B δ p M)

/-- Tensor Leibniz values are additive and balanced, hence descend at every finite adic stage. -/
theorem baseChangeStage_laws :
    let value := scalarExtensionValue fB fC δ ε p hB hC δhat εhat hδhat hεhat φ hA hDP M conn
    (∀ m, value 0 m = 0) ∧
    (∀ s t m, value (s + t) m = value s m + value t m) ∧
    (∀ s, value s 0 = 0) ∧
    (∀ s m n, value s (m + n) = value s m + value s n) ∧
    (∀ (r : completedRingB B p) s m, value (φ r * s) m = value s (r • m)) := sorry

/-- The additive tensor-product connection obtained by descending its balanced Leibniz values. -/
private def baseChangeTensor :
    scalarExtensionTensor φ M →+
      completedTensorB (completedRingB C p) p (completedScalarExtension φ p M)
        (DividedPowerDifferential.originalCompletion fC ε p) :=
  let laws := baseChangeStage_laws fB fC δ ε p hB hC δhat εhat hδhat hεhat φ hA hDP M conn
  let value := scalarExtensionValue fB fC δ ε p hB hC δhat εhat hδhat hεhat φ hA hDP M conn
  -- Local instance justification (noncanonical choice): the tensor scalar action is induced by the specified coefficient extension homomorphism.
  letI := φ.toAlgebra
  let pairing : completedRingB C p →+ M →+
      completedTensorB (completedRingB C p) p (completedScalarExtension φ p M)
        (DividedPowerDifferential.originalCompletion fC ε p) :=
    { toFun := fun s ↦ { toFun := value s, map_zero' := laws.2.2.1 s, map_add' := laws.2.2.2.1 s }
      map_zero' := AddMonoidHom.ext laws.1
      map_add' := fun s t ↦ AddMonoidHom.ext (laws.2.1 s t) }
  TensorProduct.liftAddHom pairing laws.2.2.2.2

/-- The continuous extension of the tensor-product connection to completed coefficients. -/
private def baseChangeMap :
    completedScalarExtension φ p M →+
      completedTensorB (completedRingB C p) p (completedScalarExtension φ p M)
        (DividedPowerDifferential.originalCompletion fC ε p) :=
  AdicCompletion.extendCompleteAddMap (completedRingB C p) p
    (baseChangeTensor fB fC δ ε p hB hC δhat εhat hδhat hεhat φ hA hDP M conn)

/-- Continuous scalar extension of a completed-valued connection satisfies the target Leibniz identity. -/
theorem baseChange_leibniz
    (scalar : completedRingB C p) (m : completedScalarExtension φ p M) :
    let map := baseChangeMap fB fC δ ε p hB hC δhat εhat hδhat hεhat φ hA hDP M conn
    map (scalar • m) = scalar • map m +
      AdicCompletion.of (Ideal.span {(p : completedRingB C p)}) _
        (m ⊗ₜ[completedRingB C p]
          AdicCompletion.completeAddMap C C p (dividedPowerDifferentialDerivation fC ε).toAddMonoidHom scalar) := sorry

/-- Completed scalar extension of a genuine completed-valued connection along a compatible divided-power homomorphism. -/
def baseChange :
    -- Local instance justification (noncanonical choice): the target connection is relative to the specified target base homomorphism.
    letI := fC.toAlgebra
    Adic A C ε p (completedScalarExtension φ p M) :=
  -- Local instance justification (noncanonical choice): the target connection is relative to the specified target base homomorphism.
  letI := fC.toAlgebra
  { toAddMonoidHom := baseChangeMap fB fC δ ε p hB hC δhat εhat hδhat hεhat φ hA hDP M conn
    leibniz := baseChange_leibniz fB fC δ ε p hB hC δhat εhat hδhat hεhat φ hA hDP M conn }

/-- On a pure coefficient tensor, completed scalar extension is given by the tensor Leibniz formula. -/
theorem baseChange_tmul (s : completedRingB C p) (m : M) :
    -- Local instance justification (noncanonical choice): evaluating the target connection uses its specified base homomorphism.
    letI := fC.toAlgebra
    (baseChange fB fC δ ε p hB hC δhat εhat hδhat hεhat φ hA hDP M conn).toAddMonoidHom
        (AdicCompletion.of (Ideal.span {(p : completedRingB C p)}) _
          (s • coefficientInclude p φ M m)) =
      scalarExtensionValue fB fC δ ε p hB hC δhat εhat hδhat hεhat φ hA hDP M conn s m := sorry

/-- Intrinsic curvature zero is preserved by completed scalar extension. -/
theorem baseChange_isIntegrable
    (hconn :
      -- Local instance justification (noncanonical choice): intrinsic integrability uses the specified source base homomorphism.
      letI := fB.toAlgebra
      IsIntegrable A B δ p conn) :
    -- Local instance justification (noncanonical choice): target intrinsic integrability uses the specified target base homomorphism.
    letI := fC.toAlgebra
    IsIntegrable A C ε p (baseChange fB fC δ ε p hB hC δhat εhat hδhat hεhat φ hA hDP M conn) := sorry

variable {N : ModuleCat.{u} (completedRingB B p)}
variable (connN :
  -- Local instance justification (noncanonical choice): the second connection has the specified source base homomorphism.
  letI := fB.toAlgebra
  Adic A B δ p N)
variable (g :
  -- Local instance justification (noncanonical choice): horizontal source morphisms are relative to the specified source base homomorphism.
  letI := fB.toAlgebra
  Hom conn connN)

/-- The completed extension of a horizontal coefficient map is horizontal. -/
theorem baseChangeHom_commutes (m : completedScalarExtension φ p M) :
    -- Local instance justification (noncanonical choice): evaluating the target connections uses their specified base homomorphism.
    letI := fC.toAlgebra
    -- Local instance justification (noncanonical choice): the source horizontal morphism is relative to its specified base homomorphism.
    letI := fB.toAlgebra
    let map := (completedScalarExtensionMap φ p (ModuleCat.ofHom g.toLinearMap)).hom
    (baseChange fB fC δ ε p hB hC δhat εhat hδhat hεhat φ hA hDP N connN).toAddMonoidHom (map m) =
      tensorMap (δ := ε) map
        ((baseChange fB fC δ ε p hB hC δhat εhat hδhat hεhat φ hA hDP M conn).toAddMonoidHom m) := sorry

/-- Completed scalar extension acts on horizontal coefficient homomorphisms. -/
def baseChangeHom :
    -- Local instance justification (noncanonical choice): the target horizontal morphism uses the specified target base homomorphism.
    letI := fC.toAlgebra
    Hom (baseChange fB fC δ ε p hB hC δhat εhat hδhat hεhat φ hA hDP M conn)
      (baseChange fB fC δ ε p hB hC δhat εhat hδhat hεhat φ hA hDP N connN) :=
  -- Local instance justification (noncanonical choice): the target horizontal morphism uses the specified target base homomorphism.
  letI := fC.toAlgebra
  -- Local instance justification (noncanonical choice): the source horizontal morphism is relative to its specified base homomorphism.
  letI := fB.toAlgebra
  { toLinearMap := (completedScalarExtensionMap φ p (ModuleCat.ofHom g.toLinearMap)).hom
    commutes := baseChangeHom_commutes fB fC δ ε p hB hC δhat εhat hδhat hεhat φ hA hDP M conn connN g }

end Connections

section Coherence

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable (f : R →+* S) (g : S →+* T) (p : ℕ) (M : ModuleCat.{u} R)

/-- Inclusion of the inner scalar tensor into the direct scalar tensor. -/
private def assocInner : scalarExtensionTensor f M →+
    scalarExtensionTensor (g.comp f) M :=
  (((ModuleCat.extendScalarsComp f g).inv.app M).hom.toAddMonoidHom).comp
    (((ModuleCat.extendRestrictScalarsAdj g).unit.app (scalarExtensionTensor f M)).hom.toAddMonoidHom)

/-- Continuous inclusion of the completed inner scalar tensor into the direct completion. -/
private def assocInnerCompleted : completedScalarExtension f p M →+
    completedScalarExtension (g.comp f) p M :=
  AdicCompletion.completeAddMap S T p (assocInner f g M)

/-- The balanced pairing underlying associativity of completed scalar extension. -/
private def assocPairing : T →+ completedScalarExtension f p M →+
    completedScalarExtension (g.comp f) p M :=
  { toFun := fun t ↦
      { toFun := fun v ↦ t • assocInnerCompleted f g p M v
        map_zero' := (congrArg (fun v ↦ t • v) (map_zero _)).trans (smul_zero t)
        map_add' := fun v w ↦
          (congrArg (fun v ↦ t • v) (map_add _ v w)).trans (smul_add t _ _) }
    map_zero' := AddMonoidHom.ext (fun v ↦ zero_smul T _)
    map_add' := fun t t' ↦ AddMonoidHom.ext (fun v ↦ add_smul t t' _) }

/-- The direct scalar extension maps into the iterated one by the actual inner completion map. -/
private def assocInverse :
    completedScalarExtension (g.comp f) p M →ₗ[T]
      completedScalarExtension g p (completedScalarExtension f p M) :=
  (AdicCompletion.map (Ideal.span {(p : T)})
    (((ModuleCat.extendScalars g).map
      (ModuleCat.ofHom (AdicCompletion.of (Ideal.span {(p : S)}) (scalarExtensionTensor f M)))).hom.comp
      ((ModuleCat.extendScalarsComp f g).hom.app M).hom)).restrictScalars T

/-- The associative contraction obtained from the balanced pairing, then continuously extended. -/
private def assocForward
    (hbalance : ∀ (r : S) (t : T) (v : completedScalarExtension f p M),
      assocPairing f g p M (g r * t) v = assocPairing f g p M t (r • v)) :
    completedScalarExtension g p (completedScalarExtension f p M) →+
      completedScalarExtension (g.comp f) p M :=
  -- Local instance justification (noncanonical choice): the outer tensor uses the specified scalar-extension homomorphism.
  letI := g.toAlgebra
  AdicCompletion.extendCompleteAddMap T p
    (TensorProduct.liftAddHom (assocPairing f g p M) hbalance)

/-- Completed scalar tensors are balanced, and the continuous associativity maps are mutually inverse and linear. -/
theorem completedScalarExtensionAssoc_laws :
    (∀ (r : S) (t : T) (v : completedScalarExtension f p M),
      assocPairing f g p M (g r * t) v = assocPairing f g p M t (r • v)) ∧
    (∀ hbalance,
      (∀ (t : T) v, assocForward f g p M hbalance (t • v) =
        t • assocForward f g p M hbalance v) ∧
      Function.LeftInverse (assocForward f g p M hbalance) (assocInverse f g p M) ∧
      Function.RightInverse (assocForward f g p M hbalance) (assocInverse f g p M)) := sorry

/-- The canonical associativity equivalence for completed scalar tensors. -/
def completedScalarExtensionAssoc :
    completedScalarExtension g p (completedScalarExtension f p M) ≃ₗ[T]
      completedScalarExtension (g.comp f) p M :=
  let laws := completedScalarExtensionAssoc_laws f g p M
  { toFun := assocForward f g p M laws.1
    invFun := assocInverse f g p M
    left_inv := (laws.2 laws.1).2.2
    right_inv := (laws.2 laws.1).2.1
    map_add' := (assocForward f g p M laws.1).map_add
    map_smul' := (laws.2 laws.1).1 }

/-- Identity scalar extension followed by completion is the completion of the original module. -/
private def idForward : completedScalarExtension (RingHom.id R) p M →ₗ[R]
    AdicCompletion (Ideal.span {(p : R)}) M :=
  (AdicCompletion.map (Ideal.span {(p : R)}) ((ModuleCat.extendScalarsId R).hom.app M).hom).restrictScalars R

/-- The inverse identity scalar extension inserts the unit tensor before completion. -/
private def idInverse : M →ₗ[R] completedScalarExtension (RingHom.id R) p M :=
  (AdicCompletion.of (Ideal.span {(p : R)}) _).comp
    ((ModuleCat.extendScalarsId R).inv.app M).hom

/-- Completion and identity scalar extension agree on a complete coefficient module. -/
theorem completedScalarExtensionId_laws
    (hcomplete : IsAdicComplete (Ideal.span {(p : R)}) M) :
    let forward :=
      (LinearEquiv.ofBijective (AdicCompletion.of (Ideal.span {(p : R)}) M)
        (AdicCompletion.of_bijective_iff.mpr hcomplete)).symm.toLinearMap.comp
          (idForward p M)
    Function.LeftInverse forward (idInverse p M) ∧
      Function.RightInverse forward (idInverse p M) := sorry

/-- Identity completed scalar extension of a complete module has its canonical explicit equivalence. -/
def completedScalarExtensionId
    (hcomplete : IsAdicComplete (Ideal.span {(p : R)}) M) :
    completedScalarExtension (RingHom.id R) p M ≃ₗ[R] M :=
  let forward :=
    (LinearEquiv.ofBijective (AdicCompletion.of (Ideal.span {(p : R)}) M)
      (AdicCompletion.of_bijective_iff.mpr hcomplete)).symm.toLinearMap.comp (idForward p M)
  let laws := completedScalarExtensionId_laws p M hcomplete
  { toFun := forward
    invFun := idInverse p M
    left_inv := laws.2
    right_inv := laws.1
    map_add' := forward.map_add
    map_smul' := forward.map_smul }

end Coherence

end Connection.Adic

variable {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (I : Ideal A) (γ : DividedPowers I)
variable {C : Type u} [CommRing C] [Algebra A C]
variable {P' : Type u} [CommRing P'] [Algebra A P']
variable (π' : P' →ₐ[A] C)
variable (hπ' : Function.Surjective π')
variable (J' : Ideal P')
variable (hJ' : J' = RingHom.ker π'.toRingHom)
variable (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable (hIJ' : Ideal.map (algebraMap A P') I ≤ J')
variable (E' : DividedPowerEnvelope I γ (algebraMap A P') J' hIJ')
variable (hE' : DividedPowerEnvelope.IsUniversal γ (algebraMap A P') hIJ' E')

namespace DividedPowerEnvelope.PolynomialRetract

variable [Algebra.Smooth A P']
variable (R : PolynomialRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')

/-- Completed one-forms of the original polynomial envelope. -/
abbrev omegaPoly := Coordinates.completedForms R.E p

/-- Completed one-forms of the original smooth envelope. -/
abbrev omegaSmooth (R : PolynomialRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :=
  DividedPowerDifferential.originalCompletion
    (E'.toD.comp (algebraMap A P')) E'.D.dividedPowers p

/-- Nilpotence in the distinguished quotient follows from the crystalline envelope bound. -/
private def quotientNilpotent : IsNilpotent (p : E'.D ⧸ E'.D.ideal) :=
  let bound := DividedPowers.PAdic.pAdicCompletionIsCrisWedgeObject p A P' I γ C
    (algebraMap A C) π'.toRingHom π'.comp_algebraMap hIC J' hJ' hπ' hpnil E' hE'
  ⟨bound.choose,
    (map_pow (Ideal.Quotient.mk E'.D.ideal) (p : E'.D) bound.choose).symm.trans
      ((Ideal.Quotient.eq_zero_iff_mem).mpr
        (bound.choose_spec.2.choose
          (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton (p : E'.D))) bound.choose)))⟩

/-- Differential pullback along the polynomial-to-smooth retract map, expressed on original completed forms. -/
def formsA : R.omegaPoly →ₛₗ[R.a] R.omegaSmooth :=
  Connection.Adic.originalFormsMap
    (R.E.toD.comp (algebraMap A (MvPolynomial (polynomialIndex R.n) A)))
    (E'.toD.comp (algebraMap A P')) R.E.D.dividedPowers E'.D.dividedPowers p
    (quotientNilpotent p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
    (quotientNilpotent p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    R.γbar R.γbar' R.γbar_extends R.γbar'_extends R.a R.a_base R.a_isDP

/-- Differential pullback along the smooth-to-polynomial section, expressed on original completed forms. -/
def formsB : R.omegaSmooth →ₛₗ[R.b] R.omegaPoly :=
  Connection.Adic.originalFormsMap
    (E'.toD.comp (algebraMap A P'))
    (R.E.toD.comp (algebraMap A (MvPolynomial (polynomialIndex R.n) A)))
    E'.D.dividedPowers R.E.D.dividedPowers p
    (quotientNilpotent p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    (quotientNilpotent p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
    R.γbar' R.γbar R.γbar'_extends R.γbar_extends R.b R.b_base R.b_isDP

end DividedPowerEnvelope.PolynomialRetract
