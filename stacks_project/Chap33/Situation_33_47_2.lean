module

public import ReasLib.AlgebraicGeometry.LinearSystem.UniversalDivisor
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Sections
public import stacks_project.Chap33.Lemma_33_47_1
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry.LinearSystem

variable {k : Type} [Field k]
variable {V : Type} [AddCommGroup V] [Module k V] {r : ℕ}

/-- The `k`-module structure on global sections induced by the structure morphism to `Spec(k)`,
retained for the unbundled linear-map compatibility surface. -/
noncomputable instance schemeModuleSectionsModuleOverBaseField
    (X : Over (Spec (CommRingCat.of k))) (ℒ : X.left.Modules) :
    Module k Γ(ℒ, ⊤) :=
  Scheme.Hom.globalSectionsModuleOverField X.hom ℒ

/-- Compatibility spelling of the section on `X_K` associated to an unbundled linear map and a
scalar-extended vector. -/
noncomputable abbrev baseChangeSection
    (X : Over (Spec (CommRingCat.of k)))
    (K : Type) [Field K] [Algebra k K]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
    (ψ : V →ₗ[k] Γ(ℒ, ⊤)) (b : Module.Basis (Fin r) k V) (v : V ⊗[k] K) :
    ((Scheme.Modules.pullback (FieldExtension.toSource k K X.hom)).obj ℒ).sections :=
  baseChangeSectionOfHom X K ℒ
    (@ModuleCat.ofHom k _ V Γ(ℒ, ⊤) _ _ _
      (schemeModuleSectionsModuleOverBaseField X ℒ) ψ :
        ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom ℒ) b v

/-- Compatibility spelling of the zero scheme associated to an unbundled linear map and a
scalar-extended vector. -/
noncomputable abbrev fiberDivisor
    (X : Over (Spec (CommRingCat.of k)))
    (K : Type) [Field K] [Algebra k K]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
    (ψ : V →ₗ[k] Γ(ℒ, ⊤)) (b : Module.Basis (Fin r) k V) (v : V ⊗[k] K) :
    Scheme :=
  fiberDivisorOfHom X K ℒ
    (@ModuleCat.ofHom k _ V Γ(ℒ, ⊤) _ _ _
      (schemeModuleSectionsModuleOverBaseField X ℒ) ψ :
        ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom ℒ) b v

end AlgebraicGeometry.LinearSystem

/- Situation 33.47.2: a finite-dimensional linear system with a chosen basis defines a universal
divisor on affine parameter space times `X`; over every field-valued parameter its fibre is the
zero scheme of the corresponding base-changed section, and a property holds for general vectors
when one nonempty Zariski-open parameter locus works over every field extension. -/
@[stacks 0G47] #check
  (@AlgebraicGeometry.LinearSystem.pullback_universalDivisorProjection_isIsomorphic_fiberDivisor :
    ∀ {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] {r : ℕ}
      (X : Over (Spec (CommRingCat.of k))) (K : Type) [Field K] [Algebra k K]
      (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
      (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom ℒ)
      (b : Module.Basis (Fin r) k V)
      (x : AlgebraicGeometry.LinearSystem.AffineParameterPoint k K r),
      IsIsomorphic
        (Limits.pullback
          (AlgebraicGeometry.LinearSystem.universalDivisorProjection X ℒ ψ b) x.toPoint)
        (AlgebraicGeometry.LinearSystem.fiberDivisorOfHom X K ℒ ψ b
          (AlgebraicGeometry.LinearSystem.pointVector b x)))

#check
  (@AlgebraicGeometry.LinearSystem.universalDivisor :
    ∀ {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] {r : ℕ}
      (X : Over (Spec (CommRingCat.of k))) (ℒ : X.left.Modules)
      [Scheme.Modules.Invertible ℒ]
      (_ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom ℒ)
      (_ : Module.Basis (Fin r) k V), Scheme)

#check
  (@AlgebraicGeometry.LinearSystem.HoldsForGeneralVector :
    ∀ {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] {r : ℕ}
      (_ : Module.Basis (Fin r) k V)
      (_ : ∀ (K : Type) [Field K] [Algebra k K], V ⊗[k] K → Prop), Prop)
