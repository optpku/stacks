/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.BasicOpen

/-!
# Maps of the actual Serre twisting sheaves

The map is induced by sending a homogeneous fraction a/s to ψ(a)/ψ(s).
It acts on the locally representable point-families defining the associated
sheaf. No selected ProjTwistPresentation or arbitrary twist comparison is an
input. Full natural domain is used here; tensor-product base change has that
property, without a flatness or degree-one-generation hypothesis.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u v w

namespace AlgebraicGeometry.Proj.AssociatedModule.GradedMap

variable {R : Type v} {R' : Type w} [CommRing R] [CommRing R']
variable {A B : Type (max u v w)} [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R' B]
variable {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule R' B}
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- The actual translated regular grading defining a Serre twist. -/
abbrev regularShift {R : Type v} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) (n : ℤ) :=
  GradedModule.shiftGrading (DirectSum.Decomposition.natToIntGrading 𝒜) n

/-- The fraction map is a quotient lift of the actual numerator/denominator map. -/
def fractionMap (ψ : 𝒜 →+*ᵍ ℬ) (P : Submonoid A) (Q : Submonoid B)
    (h : ∀ s : P, ψ (s : A) ∈ Q) (x : LocalizedModule P A) : LocalizedModule Q B :=
  LocalizedModule.liftOn x
    (fun p ↦ LocalizedModule.mk (ψ p.1) ⟨ψ (p.2 : A), h p.2⟩) sorry

/-- On representatives this is precisely a/s ↦ ψ(a)/ψ(s). -/
theorem fractionMap_mk (ψ : 𝒜 →+*ᵍ ℬ) (P : Submonoid A) (Q : Submonoid B)
    (h : ∀ s : P, ψ (s : A) ∈ Q) (a : A) (s : P) :
    fractionMap.{u, v, w} ψ P Q h (LocalizedModule.mk a s) =
      LocalizedModule.mk (ψ a) ⟨ψ (s : A), h s⟩ :=
  LocalizedModule.liftOn_mk _ _ _

/-- A graded ring map preserves the shifted degree-zero homogeneous part. -/
theorem fractionMap_mem (ψ : 𝒜 →+*ᵍ ℬ) (P : Submonoid A) (Q : Submonoid B)
    (h : ∀ s : P, ψ (s : A) ∈ Q) (n : ℤ)
    (x : localization 𝒜 (regularShift.{max u v w, v} 𝒜 n) P) :
    fractionMap.{u, v, w} ψ P Q h x ∈ localization ℬ (regularShift.{max u v w, w} ℬ n) Q := sorry

/-- The induced map of the actual homogeneous localized modules. -/
def localizedTwistMap (ψ : 𝒜 →+*ᵍ ℬ) (P : Submonoid A) (Q : Submonoid B)
    (h : ∀ s : P, ψ (s : A) ∈ Q) (n : ℤ) :
    localization 𝒜 (regularShift.{max u v w, v} 𝒜 n) P → localization ℬ (regularShift.{max u v w, w} ℬ n) Q :=
  fun x ↦ ⟨fractionMap.{u, v, w} ψ P Q h x, fractionMap_mem.{u, v, w} ψ P Q h n x⟩

/-- The full-domain scheme map, constructed from the standard-open localization maps. -/
def fullMap (ψ : 𝒜 →+*ᵍ ℬ) (hTop : projMapDomain ψ = ⊤) : Proj ℬ ⟶ Proj 𝒜 :=
  (Scheme.topIso (Proj ℬ)).inv ≫ ((Proj ℬ).isoOfEq hTop.symm).hom ≫ projMapMap ψ

/-- The canonical point map sends the target homogeneous prime to its inverse image. -/
theorem maps_primeCompl (ψ : 𝒜 →+*ᵍ ℬ) (hTop : projMapDomain ψ = ⊤)
    (x : Proj ℬ) :
    ∀ s : ((fullMap.{u, v, w} ψ hTop) x).asHomogeneousIdeal.toIdeal.primeCompl,
      ψ (s : A) ∈ x.asHomogeneousIdeal.toIdeal.primeCompl := sorry

/-- Apply the fraction map at each point of a scheme-map inverse image open. -/
def pointFamily (ψ : 𝒜 →+*ᵍ ℬ) (hTop : projMapDomain ψ = ⊤)
    (n : ℤ) (U : (Proj 𝒜).Opens) (s : sections 𝒜 (regularShift.{max u v w, v} 𝒜 n) U) :
    PointFamily ℬ (regularShift.{max u v w, w} ℬ n) ((fullMap.{u, v, w} ψ hTop) ⁻¹ᵁ U) :=
  fun x ↦ localizedTwistMap.{u, v, w} ψ
    (((fullMap.{u, v, w} ψ hTop) x.1).asHomogeneousIdeal.toIdeal.primeCompl)
    x.1.asHomogeneousIdeal.toIdeal.primeCompl (maps_primeCompl.{u, v, w} ψ hTop x.1) n
    (s.1 ⟨(fullMap.{u, v, w} ψ hTop) x.1, x.2⟩)

/-- Images of local homogeneous-fraction representatives remain local representatives. -/
theorem pointFamily_isLocallyRepresentable (ψ : 𝒜 →+*ᵍ ℬ)
    (hTop : projMapDomain ψ = ⊤) (n : ℤ) (U : (Proj 𝒜).Opens)
    (s : sections 𝒜 (regularShift.{max u v w, v} 𝒜 n) U) :
    IsLocallyRepresentable ℬ (regularShift.{max u v w, w} ℬ n) ((fullMap.{u, v, w} ψ hTop) ⁻¹ᵁ U)
      (pointFamily.{u, v, w} ψ hTop n U s) := sorry

/-- The actual map on homogeneous-fraction sections. -/
def sectionMap (ψ : 𝒜 →+*ᵍ ℬ) (hTop : projMapDomain ψ = ⊤)
    (n : ℤ) (U : (Proj 𝒜).Opens) (s : sections 𝒜 (regularShift.{max u v w, v} 𝒜 n) U) :
    sections ℬ (regularShift.{max u v w, w} ℬ n) ((fullMap.{u, v, w} ψ hTop) ⁻¹ᵁ U) :=
  ⟨pointFamily.{u, v, w} ψ hTop n U s, pointFamily_isLocallyRepresentable.{u, v, w} ψ hTop n U s⟩

/-- Sections of the specified Serre sheaf are its defining homogeneous-fraction sections. -/
def sourceSectionEquiv (n : ℤ) (U : (Proj 𝒜).Opens) :
    (twistingSheaf 𝒜 n).val.obj (op U) ≃ sections 𝒜 (regularShift.{max u v w, v} 𝒜 n) U := Equiv.refl _

/-- Scheme direct image evaluates the target's actual sections on the inverse image open. -/
def targetSectionEquiv (ψ : 𝒜 →+*ᵍ ℬ) (hTop : projMapDomain ψ = ⊤)
    (n : ℤ) (U : (Proj 𝒜).Opens) :
    ((Scheme.Modules.pushforward (fullMap.{u, v, w} ψ hTop)).obj (twistingSheaf ℬ n)).val.obj (op U) ≃
      sections ℬ (regularShift.{max u v w, w} ℬ n) ((fullMap.{u, v, w} ψ hTop) ⁻¹ᵁ U) := Equiv.refl _

/-- Linearization of the actual fraction map over each source open. -/
def directImageApp (ψ : 𝒜 →+*ᵍ ℬ) (hTop : projMapDomain ψ = ⊤)
    (n : ℤ) (U : ((Proj 𝒜).Opens)ᵒᵖ) :
    (twistingSheaf 𝒜 n).val.obj U ⟶
      ((Scheme.Modules.pushforward (fullMap.{u, v, w} ψ hTop)).obj (twistingSheaf ℬ n)).val.obj U := by
  let M := (twistingSheaf 𝒜 n).val.obj U
  let N := ((Scheme.Modules.pushforward (fullMap.{u, v, w} ψ hTop)).obj (twistingSheaf ℬ n)).val.obj U
  exact @ModuleCat.ofHom ((Proj 𝒜).ringCatSheaf.obj.obj U) _ M N
    M.isAddCommGroup M.isModule N.isAddCommGroup N.isModule
    { toFun := fun s ↦ (targetSectionEquiv.{u, v, w} ψ hTop n U.unop).symm
        (sectionMap.{u, v, w} ψ hTop n U.unop (sourceSectionEquiv.{u, v, w} n U.unop s))
      map_add' := sorry
      map_smul' := sorry }

/-- The morphism to direct image is the sheaf map induced on actual fraction sections. -/
def directImageHom (ψ : 𝒜 →+*ᵍ ℬ) (hTop : projMapDomain ψ = ⊤) (n : ℤ) :
    twistingSheaf 𝒜 n ⟶
      (Scheme.Modules.pushforward (fullMap.{u, v, w} ψ hTop)).obj (twistingSheaf ℬ n) where
  val := { app := directImageApp.{u, v, w} ψ hTop n, naturality := sorry }

/-- The canonical comparison is the adjoint of that specified sheaf map. -/
def hom (ψ : 𝒜 →+*ᵍ ℬ) (hTop : projMapDomain ψ = ⊤) (n : ℤ) :
    (Scheme.Modules.pullback (fullMap.{u, v, w} ψ hTop)).obj (twistingSheaf 𝒜 n) ⟶ twistingSheaf ℬ n :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (fullMap.{u, v, w} ψ hTop)).homEquiv _ _).symm
    (directImageHom.{u, v, w} ψ hTop n)

end AlgebraicGeometry.Proj.AssociatedModule.GradedMap
