/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme

/-!
# Universal divisors of linear systems

A basis of a finite-dimensional linear system gives an affine parameter space. This file
constructs its universal section and zero scheme, describes the section associated to a
field-valued parameter, and records the resulting fibre identification.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry.LinearSystem

variable {k : Type} [Field k]
variable {V : Type} [AddCommGroup V] [Module k V] {r : ℕ}

/-- A field-valued point of affine parameter space, together with its compatibility with the
fixed field extension. -/
structure AffineParameterPoint (k K : Type) [Field k] [Field K] [Algebra k K]
    (r : ℕ) where
  /-- The underlying morphism from `Spec(K)` to affine parameter space. -/
  toPoint : Spec (CommRingCat.of K) ⟶ 𝔸(Fin r; Spec (CommRingCat.of k))
  /-- The point lies over the morphism `Spec(K) ⟶ Spec(k)` induced by the field extension. -/
  commutes :
    toPoint ≫ (𝔸(Fin r; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) =
      FieldExtension.specMap k K

/-- The vector corresponding to a field-valued affine parameter point in a chosen basis. -/
noncomputable def pointVector
    {K : Type} [Field K] [Algebra k K]
    (b : Module.Basis (Fin r) k V) (x : AffineParameterPoint k K r) :
    V ⊗[k] K :=
  ∑ i, b i ⊗ₜ[k]
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom
      (x.toPoint.appTop.hom (AffineSpace.coord (Spec (CommRingCat.of k)) i))

/-- The affine point vector is the sum of the chosen basis vectors weighted by the point's
coordinates. -/
theorem pointVector_eq_sum
    {K : Type} [Field K] [Algebra k K]
    (b : Module.Basis (Fin r) k V) (x : AffineParameterPoint k K r) :
    pointVector b x =
      ∑ i, b i ⊗ₜ[k]
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom
          (x.toPoint.appTop.hom (AffineSpace.coord (Spec (CommRingCat.of k)) i)) :=
  rfl

/-- Field-valued affine parameter points correspond bijectively to vectors after scalar
extension, once a basis has been chosen. -/
theorem pointVector_bijective
    (K : Type) [Field K] [Algebra k K]
    (b : Module.Basis (Fin r) k V) :
    Function.Bijective
      (pointVector b : AffineParameterPoint k K r → V ⊗[k] K) := sorry

/-- A field-valued point of an open subset of affine parameter space, compatible with the fixed
field extension. -/
structure AffineParameterOpenPoint
    (k : Type) [Field k]
    (U : (𝔸(Fin r; Spec (CommRingCat.of k))).Opens)
    (K : Type) [Field K] [Algebra k K] where
  /-- The underlying point of the open subscheme. -/
  toPoint : Spec (CommRingCat.of K) ⟶ U
  /-- The induced affine-space point lies over `Spec(K) ⟶ Spec(k)`. -/
  commutes :
    toPoint ≫ U.ι ≫
        (𝔸(Fin r; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) =
      FieldExtension.specMap k K

/-- The parameter-space product `𝔸^r_k ×_k X`. -/
abbrev parameterSpace (X : Over (Spec (CommRingCat.of k))) : Scheme :=
  Limits.pullback
    (𝔸(Fin r; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) X.hom

/-- The projection from `𝔸^r_k ×_k X` to `X`. -/
abbrev parameterSpaceProjection (X : Over (Spec (CommRingCat.of k))) :
    (@parameterSpace k _ r X) ⟶ X.left :=
  Limits.pullback.snd
    (𝔸(Fin r; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) X.hom

/-- The projection from `𝔸^r_k ×_k X` to affine parameter space. -/
abbrev parameterSpaceAffineProjection (X : Over (Spec (CommRingCat.of k))) :
    (@parameterSpace k _ r X) ⟶ 𝔸(Fin r; Spec (CommRingCat.of k)) :=
  Limits.pullback.fst
    (𝔸(Fin r; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) X.hom

section Universal

variable (X : Over (Spec (CommRingCat.of k)))

/-- The pullback to `𝔸^r_k ×_k X` of the `i`th affine coordinate. -/
noncomputable abbrev parameterCoordinate
    (i : Fin r) : Γ(@parameterSpace k _ r X, ⊤) :=
  (parameterSpaceAffineProjection X).appTop.hom
    (AffineSpace.coord (Spec (CommRingCat.of k)) i)

/-- The pullback to `𝔸^r_k ×_k X` of the section obtained by applying a bundled linear
system to a basis vector. -/
noncomputable abbrev pullbackBasisSection
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom ℒ)
    (b : Module.Basis (Fin r) k V) (i : Fin r) :
    Γ(((Scheme.Modules.pullback (@parameterSpaceProjection k _ r X)).obj ℒ), ⊤) :=
  (Scheme.Modules.sectionsPullback (@parameterSpaceProjection k _ r X) ℒ
      (RingedSpace.sectionFromTop ℒ (ψ (b i)))).1
    (Opposite.op (⊤ : (@parameterSpace k _ r X).Opens))

/-- The universal section `∑ i, x_i ψ(b_i)` on `𝔸^r_k ×_k X`. -/
noncomputable def universalSection
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom ℒ)
    (b : Module.Basis (Fin r) k V) :
    ((Scheme.Modules.pullback (@parameterSpaceProjection k _ r X)).obj ℒ).sections :=
  RingedSpace.sectionFromTop
    ((Scheme.Modules.pullback (@parameterSpaceProjection k _ r X)).obj ℒ)
    (∑ i, parameterCoordinate X i • pullbackBasisSection X ℒ ψ b i)

/-- The universal section is definitionally the sum of coordinate-weighted basis sections. -/
theorem universalSection_eq_sum
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom ℒ)
    (b : Module.Basis (Fin r) k V) :
    universalSection X ℒ ψ b =
      RingedSpace.sectionFromTop
        ((Scheme.Modules.pullback (@parameterSpaceProjection k _ r X)).obj ℒ)
        (∑ i, parameterCoordinate X i • pullbackBasisSection X ℒ ψ b i) :=
  rfl

/-- The universal divisor is the zero scheme of the universal section on `𝔸^r_k ×_k X`. -/
noncomputable def universalDivisor
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom ℒ)
    (b : Module.Basis (Fin r) k V) : Scheme :=
  Scheme.zeroScheme
    ((Scheme.Modules.pullback (@parameterSpaceProjection k _ r X)).obj ℒ)
    (universalSection X ℒ ψ b)

/-- The universal divisor is definitionally the zero scheme of the universal section. -/
theorem universalDivisor_eq_zeroScheme
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom ℒ)
    (b : Module.Basis (Fin r) k V) :
    universalDivisor X ℒ ψ b =
      Scheme.zeroScheme
        ((Scheme.Modules.pullback (@parameterSpaceProjection k _ r X)).obj ℒ)
        (universalSection X ℒ ψ b) :=
  rfl

/-- The structural morphism from the universal divisor to affine parameter space. -/
noncomputable def universalDivisorProjection
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom ℒ)
    (b : Module.Basis (Fin r) k V) :
    universalDivisor X ℒ ψ b ⟶ 𝔸(Fin r; Spec (CommRingCat.of k)) :=
  Scheme.zeroSchemeι
      ((Scheme.Modules.pullback (@parameterSpaceProjection k _ r X)).obj ℒ)
      (universalSection X ℒ ψ b) ≫
    parameterSpaceAffineProjection X

end Universal

section BaseChange

variable (X : Over (Spec (CommRingCat.of k)))
variable (K : Type) [Field K] [Algebra k K]

/-- The `i`th coefficient of a scalar-extended vector in the chosen tensor-product basis. -/
noncomputable abbrev baseChangeCoefficient
    (b : Module.Basis (Fin r) k V) (v : V ⊗[k] K) (i : Fin r) :
    Γ(FieldExtension.baseChange k K X.hom, ⊤) :=
  (FieldExtension.toBase k K X.hom).appTop.hom
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv
      (((Algebra.TensorProduct.basis K b).repr ((TensorProduct.comm k V K) v)) i))

/-- The pullback to `X_K` of the section obtained by applying a bundled linear system to a basis
vector. -/
noncomputable abbrev baseChangeBasisSection
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom ℒ)
    (b : Module.Basis (Fin r) k V) (i : Fin r) :
    Γ(((Scheme.Modules.pullback (FieldExtension.toSource k K X.hom)).obj ℒ), ⊤) :=
  (Scheme.Modules.sectionsPullback (FieldExtension.toSource k K X.hom) ℒ
      (RingedSpace.sectionFromTop ℒ (ψ (b i)))).1
    (Opposite.op (⊤ : (FieldExtension.baseChange k K X.hom).Opens))

/-- The section on `X_K` obtained by applying a bundled linear system to a scalar-extended
vector. -/
noncomputable def baseChangeSectionOfHom
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom ℒ)
    (b : Module.Basis (Fin r) k V) (v : V ⊗[k] K) :
    ((Scheme.Modules.pullback (FieldExtension.toSource k K X.hom)).obj ℒ).sections :=
  RingedSpace.sectionFromTop
    ((Scheme.Modules.pullback (FieldExtension.toSource k K X.hom)).obj ℒ)
    (∑ i, baseChangeCoefficient X K b v i • baseChangeBasisSection X K ℒ ψ b i)

/-- The base-changed section is definitionally the sum of its coefficient-weighted basis
sections. -/
theorem baseChangeSection_eq_sum
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom ℒ)
    (b : Module.Basis (Fin r) k V) (v : V ⊗[k] K) :
    baseChangeSectionOfHom X K ℒ ψ b v =
      RingedSpace.sectionFromTop
        ((Scheme.Modules.pullback (FieldExtension.toSource k K X.hom)).obj ℒ)
        (∑ i, baseChangeCoefficient X K b v i • baseChangeBasisSection X K ℒ ψ b i) :=
  rfl

/-- The divisor on `X_K` cut out by the section associated to a scalar-extended vector. -/
noncomputable def fiberDivisorOfHom
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom ℒ)
    (b : Module.Basis (Fin r) k V) (v : V ⊗[k] K) : Scheme :=
  Scheme.zeroScheme
    ((Scheme.Modules.pullback (FieldExtension.toSource k K X.hom)).obj ℒ)
    (baseChangeSectionOfHom X K ℒ ψ b v)

/-- The divisor of a scalar-extended vector is definitionally the zero scheme of its associated
section. -/
theorem fiberDivisor_eq_zeroScheme
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom ℒ)
    (b : Module.Basis (Fin r) k V) (v : V ⊗[k] K) :
    fiberDivisorOfHom X K ℒ ψ b v =
      Scheme.zeroScheme
        ((Scheme.Modules.pullback (FieldExtension.toSource k K X.hom)).obj ℒ)
        (baseChangeSectionOfHom X K ℒ ψ b v) :=
  rfl

/-- The fibre of the universal divisor over a field-valued parameter point is isomorphic to the
zero scheme of the section associated to the corresponding scalar-extended vector. -/
theorem pullback_universalDivisorProjection_isIsomorphic_fiberDivisor
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom ℒ)
    (b : Module.Basis (Fin r) k V) (x : AffineParameterPoint k K r) :
    IsIsomorphic
      (Limits.pullback (universalDivisorProjection X ℒ ψ b) x.toPoint)
      (fiberDivisorOfHom X K ℒ ψ b (pointVector b x)) := sorry

end BaseChange

/-- A property holds for general scalar-extended vectors when one nonempty Zariski-open subset
of affine parameter space works uniformly over every field extension. -/
def HoldsForGeneralVector
    (b : Module.Basis (Fin r) k V)
    (P : ∀ (K : Type) [Field K] [Algebra k K], V ⊗[k] K → Prop) : Prop :=
  ∃ U : (𝔸(Fin r; Spec (CommRingCat.of k))).Opens,
    Set.Nonempty (U : Set (𝔸(Fin r; Spec (CommRingCat.of k)))) ∧
      ∀ (K : Type) [Field K] [Algebra k K]
        (x : AffineParameterOpenPoint k U K),
        P K (pointVector b
          { toPoint := x.toPoint ≫ U.ι
            commutes := x.commutes })

/-- The general-vector predicate unfolds to a uniform nonempty open condition on all
field-valued points. -/
theorem holdsForGeneralVector_iff
    (b : Module.Basis (Fin r) k V)
    (P : ∀ (K : Type) [Field K] [Algebra k K], V ⊗[k] K → Prop) :
    HoldsForGeneralVector b P ↔
      ∃ U : (𝔸(Fin r; Spec (CommRingCat.of k))).Opens,
        Set.Nonempty (U : Set (𝔸(Fin r; Spec (CommRingCat.of k)))) ∧
          ∀ (K : Type) [Field K] [Algebra k K]
            (x : AffineParameterOpenPoint k U K),
            P K (pointVector b
              { toPoint := x.toPoint ≫ U.ι
                commutes := x.commutes }) :=
  Iff.rfl

end AlgebraicGeometry.LinearSystem
