/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.PushforwardTensor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor.InternalHom
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape RingedSite.Hom TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

-- Local instance justification (defeq pin): moduleCat_hasDerivedCategory and SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory align DerivedCategory.singleFunctor, homologyFunctor, and canonical tensor symmetry with the coefficient-site presentation used by DerivedPushforward.derivedComplex and CanonicalTensor.tensor.
attribute [local instance] moduleCat_hasDerivedCategory
  SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

namespace AlgebraicGeometry.Scheme.DeRham.PoincareDuality

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The coefficient site on the source of the relative de Rham direct image. -/
noncomputable abbrev sourceSite :=
  RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom

/-- The coefficient site of the identity morphism on the base scheme. -/
noncomputable abbrev targetSite (S : Scheme.{u}) :=
  RingedSpace.DeRham.coefficientSite (𝟙 S : S ⟶ S).toLRSHom.toShHom

/-- The derived direct image of the relative de Rham complex. -/
noncomputable abbrev pushforward :=
  (CanonicalTensor.pushforward (DerivedPushforward.pushforwardSquare f)).obj
    (DerivedPushforward.derivedComplex f)

/-- The degree-`2 * n` cohomology module sheaf of the relative de Rham direct image. -/
noncomputable abbrev topCohomology (n : ℕ) :=
  ModuleDerived.cohomologySheaf (targetSite S) (pushforward f) (2 * (n : ℤ))

/-- The structure sheaf of the identity coefficient site, regarded as a module over itself. -/
noncomputable abbrev structureModule (S : Scheme.{u}) :=
  SheafOfModules.RingedSite.unitModule (Opens.grothendieckTopology S)
    (RingedSpace.DeRham.coefficients (𝟙 S : S ⟶ S).toLRSHom.toShHom)

/-- The structure module of the base, placed in cohomological degree zero. -/
noncomputable abbrev derivedStructureModule (S : Scheme.{u}) :=
  (DerivedCategory.singleFunctor (RingedSite.ModuleCat.{u} (targetSite S)) 0).obj
    (structureModule S)

/-- The top-cohomology map induced by a shifted derived trace. -/
noncomputable def topTrace (n : ℕ)
    (τ : (pushforward f)⟦(2 * (n : ℤ))⟧ ⟶ derivedStructureModule S) :
    topCohomology f n ⟶ structureModule S :=
  ((DerivedCategory.homologyFunctor
      (RingedSite.ModuleCat.{u} (targetSite S)) 0).shiftIso
      (2 * (n : ℤ)) 0 (2 * (n : ℤ)) (Int.add_zero _)).inv.app (pushforward f) ≫
    ModuleDerived.cohomologySheafMap (targetSite S) 0 τ ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (RingedSite.ModuleCat.{u} (targetSite S)) 0).hom.app (structureModule S)

/-- The top-cohomology trace is induced by shift, cohomology, and the single-module comparison. -/
theorem topTrace_eq (n : ℕ)
    (τ : (pushforward f)⟦(2 * (n : ℤ))⟧ ⟶ derivedStructureModule S) :
    topTrace f n τ =
      ((DerivedCategory.homologyFunctor
        (RingedSite.ModuleCat.{u} (targetSite S)) 0).shiftIso
        (2 * (n : ℤ)) 0 (2 * (n : ℤ)) (Int.add_zero _)).inv.app (pushforward f) ≫
      ModuleDerived.cohomologySheafMap (targetSite S) 0 τ ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (RingedSite.ModuleCat.{u} (targetSite S)) 0).hom.app (structureModule S) := sorry

/-- Derived tensor commutes with a shift of its second factor. -/
noncomputable def shiftSecond
    (K L : ModuleDerived.{u} (targetSite S)) (m : ℤ) :
    (CanonicalTensor.tensor (𝟙 S : S ⟶ S)).obj (K, L⟦m⟧) ≅
      ((CanonicalTensor.tensor (𝟙 S : S ⟶ S)).obj (K, L))⟦m⟧ :=
  DerivedCategory.DerivedTensor.Bifunctor.comm K (L⟦m⟧) ≪≫
    CanonicalTensor.shiftFirst (𝟙 S : S ⟶ S) L K m ≪≫
    (shiftFunctor _ m).mapIso (DerivedCategory.DerivedTensor.Bifunctor.comm L K)

/-- The shifted canonical de Rham cup product followed by a derived trace. -/
noncomputable def pairing (n : ℕ)
    (τ : (pushforward f)⟦(2 * (n : ℤ))⟧ ⟶ derivedStructureModule S) :
    (CanonicalTensor.tensor (𝟙 S : S ⟶ S)).obj
      (pushforward f, (pushforward f)⟦(2 * (n : ℤ))⟧) ⟶ derivedStructureModule S :=
  (shiftSecond (pushforward f) (pushforward f) (2 * (n : ℤ))).hom ≫
    (CanonicalTensor.cupProduct (DerivedPushforward.pushforwardSquare f))⟦(2 * (n : ℤ))⟧' ≫ τ

/-- The cup-trace pairing is the canonical second-factor shift followed by shifted cup and trace. -/
theorem pairing_eq (n : ℕ)
    (τ : (pushforward f)⟦(2 * (n : ℤ))⟧ ⟶ derivedStructureModule S) :
    pairing f n τ =
      (shiftSecond (pushforward f) (pushforward f) (2 * (n : ℤ))).hom ≫
        (CanonicalTensor.cupProduct (DerivedPushforward.pushforwardSquare f))⟦(2 * (n : ℤ))⟧' ≫ τ := sorry

/-- A derived trace is perfect when its direct image is perfect and its curried cup pairing
is an isomorphism to the derived sheaf dual of the shifted direct image. -/
def IsPerfect (n : ℕ)
    (τ : (pushforward f)⟦(2 * (n : ℤ))⟧ ⟶ derivedStructureModule S) : Prop :=
  RingedSite.Hom.ModuleDerived.IsPerfect (pushforward f) ∧
    IsIso ((ModuleDerived.Tensor.homEquiv
      (RingedSpace.DeRham.coefficients (𝟙 S : S ⟶ S).toLRSHom.toShHom)
      (pushforward f) ((pushforward f)⟦(2 * (n : ℤ))⟧)
      (derivedStructureModule S)).symm (pairing f n τ))

/-- Perfectness is equivalent to perfectness of the direct image and invertibility of the
canonical curried cup-trace pairing. -/
theorem isPerfect_iff (n : ℕ)
    (τ : (pushforward f)⟦(2 * (n : ℤ))⟧ ⟶ derivedStructureModule S) :
    IsPerfect f n τ ↔
      RingedSite.Hom.ModuleDerived.IsPerfect (pushforward f) ∧
        IsIso ((ModuleDerived.Tensor.homEquiv
          (RingedSpace.DeRham.coefficients (𝟙 S : S ⟶ S).toLRSHom.toShHom)
          (pushforward f) ((pushforward f)⟦(2 * (n : ℤ))⟧)
          (derivedStructureModule S)).symm (pairing f n τ)) := sorry

section UnitAction

/-- Multiplication by a global unit on relative differential forms. -/
noncomputable def hodgeFormUnitAction (a : Γ(X, ⊤)ˣ) (i : ℕ) :
    RingedSpace.DeRham.form.{u} f.toLRSHom.toShHom i ⟶
      RingedSpace.DeRham.form.{u} f.toLRSHom.toShHom i :=
  RingedSpace.globalSectionMul.{u} (a : Γ(X, ⊤))
    (RingedSpace.DeRham.form.{u} f.toLRSHom.toShHom i)

/-- Multiplication by a global unit on a term of the coefficient-valued relative de Rham
complex. -/
noncomputable def formUnitAction (a : Γ(X, ⊤)ˣ) (i : ℕ) :
    (DeRham.deRhamComplex f).X i ⟶ (DeRham.deRhamComplex f).X i :=
  (SheafOfModules.RingedSite.DeRham.restriction
    (RingedSpace.DeRham.structureMap f.toShHom)).map (hodgeFormUnitAction f a i)

/-- For a proper smooth morphism over a quasi-compact, quasi-separated base with nonempty
equidimensional fibres, multiplication by a global unit commutes with the relative differential. -/
theorem formUnitAction_comm (n : ℕ) [CompactSpace S] [QuasiSeparatedSpace S]
    [IsProper f] [Smooth f] [Scheme.Hom.RelativeDimension f n]
    (h_nonempty : ∀ s : S, Nonempty (f.fiber s)) (a : Γ(X, ⊤)ˣ)
    (i j : ℕ) (hij : (up ℕ).Rel i j) :
    formUnitAction f a i ≫ (DeRham.deRhamComplex f).d i j =
      (DeRham.deRhamComplex f).d i j ≫ formUnitAction f a j := sorry

/-- The chain endomorphism of the relative de Rham complex induced by a global unit. -/
noncomputable def complexUnitAction (n : ℕ) [CompactSpace S] [QuasiSeparatedSpace S]
    [IsProper f] [Smooth f] [Scheme.Hom.RelativeDimension f n]
    (h_nonempty : ∀ s : S, Nonempty (f.fiber s)) (a : Γ(X, ⊤)ˣ) :
    DeRham.deRhamComplex f ⟶ DeRham.deRhamComplex f :=
  HomologicalComplex.Hom.mk (formUnitAction f a)
    (formUnitAction_comm f n h_nonempty a)

/-- The endomorphism of `Ωᵈᴿ[X/S]` induced by multiplication by a global unit. -/
noncomputable def derivedUnitAction (n : ℕ) [CompactSpace S] [QuasiSeparatedSpace S]
    [IsProper f] [Smooth f] [Scheme.Hom.RelativeDimension f n]
    (h_nonempty : ∀ s : S, Nonempty (f.fiber s)) (a : Γ(X, ⊤)ˣ) :
    DerivedPushforward.derivedComplex f ⟶ DerivedPushforward.derivedComplex f :=
  (moduleLocalization.{u} (sourceSite f)).map
    ((HomotopyCategory.quotient _ (up ℤ)).map
      (HomologicalComplex.extendMap (complexUnitAction f n h_nonempty a) embeddingUpNat))

/-- The endomorphism of `Rf_*Ωᵈᴿ[X/S]` induced by multiplication by a global unit. -/
noncomputable def pushforwardUnitAction (n : ℕ) [CompactSpace S]
    [QuasiSeparatedSpace S] [IsProper f] [Smooth f]
    [Scheme.Hom.RelativeDimension f n]
    (h_nonempty : ∀ s : S, Nonempty (f.fiber s)) (a : Γ(X, ⊤)ˣ) :
    pushforward f ⟶ pushforward f :=
  (CanonicalTensor.pushforward (DerivedPushforward.pushforwardSquare f)).map
    (derivedUnitAction f n h_nonempty a)

/-- The action of a global unit on `R^(2 * n)f_*Ωᵈᴿ[X/S]`. -/
noncomputable def unitAction (n : ℕ) [CompactSpace S] [QuasiSeparatedSpace S]
    [IsProper f] [Smooth f] [Scheme.Hom.RelativeDimension f n]
    (h_nonempty : ∀ s : S, Nonempty (f.fiber s)) (a : Γ(X, ⊤)ˣ) :
    topCohomology f n ⟶ topCohomology f n :=
  ModuleDerived.cohomologySheafMap (targetSite S) (2 * (n : ℤ))
    (pushforwardUnitAction f n h_nonempty a)

/-- The top-cohomology unit action is induced by the pushed-forward multiplication map on the
relative de Rham complex. -/
theorem unitAction_eq (n : ℕ) [CompactSpace S] [QuasiSeparatedSpace S]
    [IsProper f] [Smooth f] [Scheme.Hom.RelativeDimension f n]
    (h_nonempty : ∀ s : S, Nonempty (f.fiber s)) (a : Γ(X, ⊤)ˣ) :
    unitAction f n h_nonempty a =
      ModuleDerived.cohomologySheafMap (targetSite S) (2 * (n : ℤ))
        (pushforwardUnitAction f n h_nonempty a) := sorry

end UnitAction

end AlgebraicGeometry.Scheme.DeRham.PoincareDuality

namespace AlgebraicGeometry.Scheme.DeRham

variable {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
variable [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [Smooth f]
variable [Scheme.Hom.RelativeDimension f n]
/-- For a proper smooth morphism over a quasi-compact, quasi-separated base with nonempty fibres of relative
dimension `n`, there is a trace inducing an `𝒪_S`-module map on
`R^(2 * n)f_*Ωᵈᴿ[X/S]` whose cup-trace pairing on `Rf_*Ωᵈᴿ[X/S]` is perfect. -/
theorem existsRelativeDeRhamPoincareTrace
    (h_nonempty : ∀ s : S, Nonempty (f.fiber s)) :
    ∃ t : PoincareDuality.topCohomology f n ⟶ PoincareDuality.structureModule S,
      ∃ τ : (PoincareDuality.pushforward f)⟦(2 * (n : ℤ))⟧ ⟶
          PoincareDuality.derivedStructureModule S,
        PoincareDuality.topTrace f n τ = t ∧ PoincareDuality.IsPerfect f n τ := sorry

/-- The induced maps on `R^(2 * n)f_*Ωᵈᴿ[X/S]` of any two
perfect traces differ by precomposition with multiplication by a unit of `Γ(X, ⊤)`. -/
theorem relativeDeRhamPoincareTrace_unique
    (h_nonempty : ∀ s : S, Nonempty (f.fiber s))
    (t t' : PoincareDuality.topCohomology f n ⟶ PoincareDuality.structureModule S)
    (τ τ' : (PoincareDuality.pushforward f)⟦(2 * (n : ℤ))⟧ ⟶
      PoincareDuality.derivedStructureModule S)
    (ht : PoincareDuality.topTrace f n τ = t)
    (ht' : PoincareDuality.topTrace f n τ' = t')
    (hτ : PoincareDuality.IsPerfect f n τ)
    (hτ' : PoincareDuality.IsPerfect f n τ') :
    ∃ a : Γ(X, ⊤)ˣ,
      t' = PoincareDuality.unitAction f n h_nonempty a ≫ t := sorry

end AlgebraicGeometry.Scheme.DeRham
