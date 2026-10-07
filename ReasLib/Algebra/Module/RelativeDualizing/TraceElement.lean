module

public import ReasLib.LinearAlgebra.Trace.Projective
public import ReasLib.Algebra.Module.RelativeDualizing.BaseChange
public import ReasLib.Algebra.Module.RelativeDualizing.Product
public import ReasLib.Algebra.Module.RelativeDualizing.Localization
public import ReasLib.RingTheory.QuasiFinite.BaseChange

@[expose] public section

noncomputable section

open AlgebraicGeometry
open Algebra.FiniteType.QuasiFinite Localization.Away.Relative
open scoped Algebra.DualModule Algebra.Product TensorProduct TensorProduct.Right

universe u

namespace Algebra.RelativeDualizingModule.TraceElement

/-- The spectrum map induced by the canonical self-algebra structure is an open
immersion. -/
instance instIsOpenImmersionSpecMapIdentity (R : Type u) [CommRing R] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R R))) := sorry

/-- A finite factor of a product presentation of a flat base change is
projective. -/
theorem leftFactorProjectiveOfBaseChange
    (A B A₁ C D : Type u)
    [CommRing A] [CommRing B] [CommRing A₁] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A A₁] [Algebra A₁ C] [Algebra A₁ D]
    [Algebra B (C × D)] [Algebra A (C × D)]
    [IsScalarTower A B (C × D)] [IsScalarTower A A₁ (C × D)]
    [Module.Flat A B] [IsNoetherianRing A₁] [Module.Finite A₁ C]
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B (C × D)).toLinearMap) :
    Module.Projective A₁ C := sorry

/-- The right factor of a product presentation of a quasi-finite base change is
quasi-finite. -/
theorem rightFactorQuasiFiniteOfBaseChange
    (A B A₁ C D : Type u)
    [CommRing A] [CommRing B] [CommRing A₁] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A A₁] [Algebra A₁ C] [Algebra A₁ D]
    [Algebra B (C × D)] [Algebra A (C × D)]
    [IsScalarTower A B (C × D)] [IsScalarTower A A₁ (C × D)]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B (C × D)).toLinearMap) :
    Algebra.FiniteType.QuasiFinite A₁ D := sorry

/-- An element of a chosen presentation of a relative dualizing module is
universal when every admissible Noetherian base change and product presentation
sends its first component to the finite-projective trace tensor. -/
def IsUniversal
    (A B' B : Type u)
    [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Flat A B] (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (τ : Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open) : Prop :=
  ∀ (A₁ C D D' : Type u)
    [CommRing A₁] [CommRing C] [CommRing D] [CommRing D']
    [IsNoetherianRing A₁] [IsNoetherianRing C] [IsNoetherianRing D]
    [Algebra A A₁] [Algebra A₁ C] [Algebra A₁ D'] [Algebra D' D]
    [Algebra A₁ D] [IsScalarTower A₁ D' D]
    [Algebra B' (C × D')] [Algebra B (C × D)]
    [Algebra A (C × D')] [IsScalarTower A B' (C × D')]
    [IsScalarTower A A₁ (C × D')]
    [Algebra A (C × D)] [IsScalarTower A B (C × D)]
    [IsScalarTower A A₁ (C × D)]
    [Algebra B' (C × D)] [IsScalarTower B' B (C × D)]
    [IsScalarTower B' (C × D') (C × D)]
    [Module.Finite A₁ C] [Module.Finite A₁ D']
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap D' D)))]
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B (C × D)).toLinearMap)
    (h_finiteModel : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B' (C × D')).toLinearMap),
    let hC : Algebra.FiniteType.QuasiFinite A₁ C :=
      Algebra.FiniteType.QuasiFinite.of_moduleFinite
    let hD : Algebra.FiniteType.QuasiFinite A₁ D :=
      rightFactorQuasiFiniteOfBaseChange A B A₁ C D h_quasiFinite h_baseChange
    let hCD := Algebra.FiniteType.QuasiFinite.prod hC hD
    (Algebra.RelativeDualizingModule.prodComparisonOf A₁ C C D' D hC hD
      (Algebra.RelativeDualizingModule.baseChangeOf A A₁ B' B (C × D') (C × D)
        h_quasiFinite hCD h_open inferInstance h_baseChange h_finiteModel τ)).1 =
      (@Algebra.FiniteProjective.trace A₁ C _ _ _ _
        (leftFactorProjectiveOfBaseChange A B A₁ C D h_baseChange)) ⊗ₜ[C] (1 : C)

/-- A universal trace element supplies its defining first-component equality
after every admissible base change and product presentation. -/
theorem IsUniversal.baseChange_fst
    (A B' B : Type u)
    [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Flat A B] (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (τ : Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open)
    (hτ : IsUniversal A B' B h_quasiFinite h_open τ)
    (A₁ C D D' : Type u)
    [CommRing A₁] [CommRing C] [CommRing D] [CommRing D']
    [IsNoetherianRing A₁] [IsNoetherianRing C] [IsNoetherianRing D]
    [Algebra A A₁] [Algebra A₁ C] [Algebra A₁ D'] [Algebra D' D]
    [Algebra A₁ D] [IsScalarTower A₁ D' D]
    [Algebra B' (C × D')] [Algebra B (C × D)]
    [Algebra A (C × D')] [IsScalarTower A B' (C × D')]
    [IsScalarTower A A₁ (C × D')]
    [Algebra A (C × D)] [IsScalarTower A B (C × D)]
    [IsScalarTower A A₁ (C × D)]
    [Algebra B' (C × D)] [IsScalarTower B' B (C × D)]
    [IsScalarTower B' (C × D') (C × D)]
    [Module.Finite A₁ C] [Module.Finite A₁ D']
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap D' D)))]
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B (C × D)).toLinearMap)
    (h_finiteModel : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B' (C × D')).toLinearMap) :
    let hC : Algebra.FiniteType.QuasiFinite A₁ C :=
      Algebra.FiniteType.QuasiFinite.of_moduleFinite
    let hD : Algebra.FiniteType.QuasiFinite A₁ D :=
      rightFactorQuasiFiniteOfBaseChange A B A₁ C D h_quasiFinite h_baseChange
    let hCD := Algebra.FiniteType.QuasiFinite.prod hC hD
    (Algebra.RelativeDualizingModule.prodComparisonOf A₁ C C D' D hC hD
      (Algebra.RelativeDualizingModule.baseChangeOf A A₁ B' B (C × D') (C × D)
        h_quasiFinite hCD h_open inferInstance h_baseChange h_finiteModel τ)).1 =
      (@Algebra.FiniteProjective.trace A₁ C _ _ _ _
        (leftFactorProjectiveOfBaseChange A B A₁ C D h_baseChange)) ⊗ₜ[C] (1 : C) := sorry


/-- Finite-type quasi-finiteness is preserved by a base change presented through
`IsBaseChange`, rather than by the canonical tensor-product model. -/
theorem quasiFiniteOfBaseChange
    (A A₁ B B₁ : Type u)
    [CommRing A] [CommRing A₁] [CommRing B] [CommRing B₁]
    [Algebra A B] [Algebra A A₁] [Algebra A₁ B₁] [Algebra B B₁]
    [Algebra A B₁] [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B B₁).toLinearMap) :
    Algebra.FiniteType.QuasiFinite A₁ B₁ := sorry

/-- A universal trace element remains universal after a Noetherian
base change presented by an `IsBaseChange` model. -/
theorem baseChange
    (A A₁ B' B B₁' B₁ : Type u)
    [CommRing A] [CommRing A₁] [CommRing B'] [CommRing B]
    [CommRing B₁'] [CommRing B₁]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsNoetherianRing A₁] [IsNoetherianRing B₁]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A₁ B₁'] [Algebra B₁' B₁] [Algebra A₁ B₁]
    [IsScalarTower A₁ B₁' B₁]
    [Algebra A A₁] [Algebra B' B₁'] [Algebra B B₁]
    [Algebra A B₁'] [IsScalarTower A B' B₁'] [IsScalarTower A A₁ B₁']
    [Algebra A B₁] [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁]
    [Algebra B' B₁] [IsScalarTower B' B B₁] [IsScalarTower B' B₁' B₁]
    [Module.Flat A B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B'] [Module.Finite A₁ B₁']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁' B₁))))
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B B₁).toLinearMap)
    (h_finiteModel : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B' B₁').toLinearMap)
    (τ : RelativeDualizingModule.of A B' B h_quasiFinite h_open)
    (hτ : IsUniversal A B' B h_quasiFinite h_open τ) :
    let h_flat₁ : Module.Flat A₁ B₁ :=
      Module.Flat.isBaseChange A A₁ B B₁ h_baseChange
    let h_quasiFinite₁ :=
      quasiFiniteOfBaseChange A A₁ B B₁ h_quasiFinite h_baseChange
    @IsUniversal A₁ B₁' B₁
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance h_flat₁
      h_quasiFinite₁ inferInstance h_open₁
      (baseChangeOf A A₁ B' B B₁' B₁ h_quasiFinite h_quasiFinite₁
        h_open h_open₁ h_baseChange h_finiteModel τ) := sorry

/-- A universal trace element over `Localization.Away f` remains
universal when viewed over the original Noetherian base ring. -/
theorem awayBase
    (A B' B : Type u)
    [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Flat A B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (f : A) [Algebra (Localization.Away f) B]
    [IsScalarTower A (Localization.Away f) B]
    [Module.Flat (Localization.Away f) B] :
    ∀ τ,
      @IsUniversal (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) B
        inferInstance inferInstance inferInstance inferInstance inferInstance
        (mapAlgebra (algebraMap A B') f)
        (awayFactorMap A B' B f).toAlgebra inferInstance
        (awayFactorMap_isScalarTower A B' B f) inferInstance
        (quasiFiniteAwayBase A B h_quasiFinite f)
        (finiteAwayBase A B' f)
        (openAwayBase A B' B h_open f) τ →
      IsUniversal A B' B h_quasiFinite h_open
        ((awayBaseIso A B' B h_quasiFinite h_open f).inv τ) := sorry

/-- Localizing the target at `g` sends a universal trace element
to a universal trace element. -/
theorem awayTarget
    (A B' B : Type u)
    [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Flat A B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (g : B) (τ : RelativeDualizingModule.of A B' B h_quasiFinite h_open)
    (hτ : IsUniversal A B' B h_quasiFinite h_open τ) :
    IsUniversal A B' (Localization.Away g)
      (quasiFiniteAwayTarget A B h_quasiFinite g)
      (openAwayTarget B' B h_open g)
      ((awayTargetIso A B' B h_quasiFinite h_open g).hom
        (LocalizedModule.mk τ 1)) := sorry

/-- A section of the relative dualizing module is a universal trace
element if its image after localizing the target at each member of a
finite family generating the unit ideal is a universal trace element. -/
theorem of_localizationAway_unitIdeal
    (A B' B : Type u)
    [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Flat A B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (m : ℕ) (g : Fin m → B) (hunit : Ideal.span (Set.range g) = ⊤)
    (τ : RelativeDualizingModule.of A B' B h_quasiFinite h_open)
    (hτ : ∀ i, IsUniversal A B' (Localization.Away (g i))
      (quasiFiniteAwayTarget A B h_quasiFinite (g i))
      (openAwayTarget B' B h_open (g i))
      ((awayTargetIso A B' B h_quasiFinite h_open (g i)).hom
        (LocalizedModule.mk τ 1))) :
    IsUniversal A B' B h_quasiFinite h_open τ := sorry

/-- The first component of a universal trace element for a product
target is a universal trace element. -/
theorem prodFst
    (A B₁' B₁ B₂' B₂ : Type u)
    [CommRing A] [CommRing B₁'] [CommRing B₁] [CommRing B₂'] [CommRing B₂]
    [IsNoetherianRing A] [IsNoetherianRing B₁] [IsNoetherianRing B₂]
    [Algebra A B₁'] [Algebra B₁' B₁] [Algebra A B₁] [IsScalarTower A B₁' B₁]
    [Algebra A B₂'] [Algebra B₂' B₂] [Algebra A B₂] [IsScalarTower A B₂' B₂]
    [Module.Flat A (B₁ × B₂)] [Module.Flat A B₁] [Module.Flat A B₂]
    (h_quasiFinite₁ : Algebra.FiniteType.QuasiFinite A B₁)
    (h_quasiFinite₂ : Algebra.FiniteType.QuasiFinite A B₂)
    [Module.Finite A B₁'] [Module.Finite A B₂']
    [h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁' B₁)))]
    [h_open₂ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₂' B₂)))]
    (τ : RelativeDualizingModule.of A (B₁' × B₂') (B₁ × B₂)
      (prod h_quasiFinite₁ h_quasiFinite₂) inferInstance)
    (hτ : IsUniversal A (B₁' × B₂') (B₁ × B₂)
      (prod h_quasiFinite₁ h_quasiFinite₂)
      inferInstance τ) :
    IsUniversal A B₁' B₁ h_quasiFinite₁ h_open₁
      (prodComparisonOf A B₁' B₁ B₂' B₂ h_quasiFinite₁ h_quasiFinite₂ τ).1 := sorry

/-- The second component of a universal trace element for a product
target is a universal trace element. -/
theorem prodSnd
    (A B₁' B₁ B₂' B₂ : Type u)
    [CommRing A] [CommRing B₁'] [CommRing B₁] [CommRing B₂'] [CommRing B₂]
    [IsNoetherianRing A] [IsNoetherianRing B₁] [IsNoetherianRing B₂]
    [Algebra A B₁'] [Algebra B₁' B₁] [Algebra A B₁] [IsScalarTower A B₁' B₁]
    [Algebra A B₂'] [Algebra B₂' B₂] [Algebra A B₂] [IsScalarTower A B₂' B₂]
    [Module.Flat A (B₁ × B₂)] [Module.Flat A B₁] [Module.Flat A B₂]
    (h_quasiFinite₁ : Algebra.FiniteType.QuasiFinite A B₁)
    (h_quasiFinite₂ : Algebra.FiniteType.QuasiFinite A B₂)
    [Module.Finite A B₁'] [Module.Finite A B₂']
    [h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁' B₁)))]
    [h_open₂ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₂' B₂)))]
    (τ : RelativeDualizingModule.of A (B₁' × B₂') (B₁ × B₂)
      (prod h_quasiFinite₁ h_quasiFinite₂) inferInstance)
    (hτ : IsUniversal A (B₁' × B₂') (B₁ × B₂)
      (prod h_quasiFinite₁ h_quasiFinite₂)
      inferInstance τ) :
    IsUniversal A B₂' B₂ h_quasiFinite₂ h_open₂
      (prodComparisonOf A B₁' B₁ B₂' B₂ h_quasiFinite₁ h_quasiFinite₂ τ).2 := sorry


/-- A flat quasi-finite algebra of Noetherian rings, presented by a finite
factorization whose spectrum map is an open immersion, admits a universal
trace element in the corresponding relative dualizing module. -/
theorem exists_of_flat_quasiFinite
    (A B' B : Type u)
    [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Flat A B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))) :
    ∃ τ : Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open,
      IsUniversal A B' B h_quasiFinite h_open τ := sorry

end Algebra.RelativeDualizingModule.TraceElement

/-- Any two universal trace elements in the same relative dualizing module are
equal. -/
theorem Algebra.RelativeDualizingModule.TraceElement.IsUniversal.eq
    {A B' B : Type u} [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Flat A B] {h_quasiFinite : Algebra.FiniteType.QuasiFinite A B}
    [Module.Finite A B']
    {h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))}
    {τ₁ τ₂ : Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open}
    (hτ₁ : Algebra.RelativeDualizingModule.TraceElement.IsUniversal
      A B' B h_quasiFinite h_open τ₁)
    (hτ₂ : Algebra.RelativeDualizingModule.TraceElement.IsUniversal
      A B' B h_quasiFinite h_open τ₂) :
    τ₁ = τ₂ := sorry

namespace Algebra.RelativeDualizingModule

/-- The finite-projective trace functional, regarded as an element of the
identity presentation of the relative dualizing module. -/
noncomputable def finiteFlatTraceElement
    (A B : Type u) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B]
    [Module.Finite A B] [Module.Flat A B] :
    RelativeDualizingModule.of A B B (.of_moduleFinite) inferInstance :=
  (@Algebra.FiniteProjective.trace A B _ _ _ _
    (Module.projectiveOfFiniteFlat A B)) ⊗ₜ[B] (1 : B)

/-- The canonical finite-flat trace element satisfies the universal base-change
and product characterization of a trace element. -/
theorem finiteFlatTraceElement_isTraceElement
    (A B : Type u) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B]
    [Module.Finite A B] [Module.Flat A B] :
    TraceElement.IsUniversal A B B (.of_moduleFinite) inferInstance
      (finiteFlatTraceElement A B) := sorry

end Algebra.RelativeDualizingModule

end
