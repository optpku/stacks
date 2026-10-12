/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap50.Lemma_50_24_4
public import stacks_project.Chap50.Remark_50_4_2
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import ReasLib.CategoryTheory.Monoidal.Closed.Braided

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open CategoryTheory.MonoidalClosed RingedSite.Hom TopologicalSpace
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.PoincareDuality

-- Local instance justification (defeq pin): align the pushed de Rham complex and its direct image with the coefficient-site presentation fixed by `derivedComplex`.
attribute [local instance] moduleCat_hasDerivedCategory

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The coefficient site on the source of the relative de Rham direct image. -/
noncomputable abbrev sourceSite :=
  RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom

/-- The coefficient site on the base of the relative de Rham direct image. -/
noncomputable abbrev targetSite (S : Scheme.{u}) :=
  RingedSpace.DeRham.coefficientSite (𝟙 S : S ⟶ S).toLRSHom.toShHom

/-- The coefficient morphism used by the identity-square specialization of the generic cup
product. -/
noncomputable abbrev cupHom :=
  RingedSpace.DeRham.baseChangeHom
    (DeRham.sheafedSquare f f (𝟙 S) (𝟙 S) (DeRham.pushforwardSquare f))

/-- The derived direct image `Rf_*Ωᵈᴿ[X/S]` on the coefficient site of `S`. -/
noncomputable abbrev pushforward [Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u} (cupHom f))
    (ModuleQis.{u} (sourceSite f))] :=
  (modulePushforwardDerived.{u} (cupHom f)).obj (DeRham.derivedComplex f)

/-- The degree-`2 * n` cohomology module sheaf of `Rf_*Ωᵈᴿ[X/S]`. -/
noncomputable abbrev topCohomology [Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u} (cupHom f))
    (ModuleQis.{u} (sourceSite f))] (n : ℕ) :=
  ModuleDerived.cohomologySheaf (targetSite S) (pushforward f) (2 * (n : ℤ))

/-- The degree-zero cohomology of the derived tensor unit, the canonical derived model of
`𝒪_S`. -/
noncomputable abbrev structureModule (S : Scheme.{u})
    [MonoidalCategory (ModuleDerived.{u} (targetSite S))] :=
  ModuleDerived.cohomologySheaf (targetSite S)
    (𝟙_ (ModuleDerived.{u} (targetSite S))) 0

section Trace

variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{u} (cupHom f))
  (ModuleQis.{u} (sourceSite f))]
variable [MonoidalCategory (ModuleDerived.{u} (targetSite S))]

/-- The map on `R^(2 * n)f_*Ωᵈᴿ[X/S]` induced by a shifted derived trace. -/
noncomputable def topTrace (n : ℕ)
    (τ : (pushforward f)⟦(2 * (n : ℤ))⟧ ⟶
      𝟙_ (ModuleDerived.{u} (targetSite S))) :
    topCohomology f n ⟶ structureModule S :=
  ((DerivedCategory.homologyFunctor
      (RingedSite.ModuleCat.{u} (targetSite S)) 0).shiftIso
      (2 * (n : ℤ)) 0 (2 * (n : ℤ)) (Int.add_zero _)).inv.app (pushforward f) ≫
    ModuleDerived.cohomologySheafMap (targetSite S) 0 τ

/-- The top-cohomology trace is the shift comparison followed by degree-zero cohomology of
the derived trace. -/
theorem topTrace_eq (n : ℕ)
    (τ : (pushforward f)⟦(2 * (n : ℤ))⟧ ⟶
      𝟙_ (ModuleDerived.{u} (targetSite S))) :
    topTrace f n τ =
      ((DerivedCategory.homologyFunctor
        (RingedSite.ModuleCat.{u} (targetSite S)) 0).shiftIso
        (2 * (n : ℤ)) 0 (2 * (n : ℤ)) (Int.add_zero _)).inv.app (pushforward f) ≫
      ModuleDerived.cohomologySheafMap (targetSite S) 0 τ := sorry

end Trace

section Pairing

variable [MonoidalCategory (ModuleDerived.{u} (sourceSite f))]
variable [Functor.LaxMonoidal (moduleLocalization.{u} (sourceSite f))]
variable [MonoidalCategory (ModuleDerived.{u} (targetSite S))]
variable [(cupHom f).modulePushforward.IsRightAdjoint]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{u} (cupHom f))
  (ModuleQis.{u} (sourceSite f))]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{u} (cupHom f))
  (ModuleQis.{u} (targetSite S))]
variable [DerivedAdjunction.HasPair.{u} (cupHom f)]
variable [(modulePullbackDerived.{u} (cupHom f)).OplaxMonoidal]
variable [((tensoringLeft (ModuleDerived.{u} (targetSite S))).obj
  (pushforward f)).CommShift ℤ]

/-- The cup product on the derived direct image of the relative de Rham complex. -/
noncomputable def cupProduct : pushforward f ⊗ pushforward f ⟶ pushforward f :=
  DeRham.cupProduct f f (𝟙 S) (𝟙 S) (DeRham.pushforwardSquare f)

/-- The whole-complex cup product is the identity-square specialization of the relative cup
product. -/
theorem cupProduct_eq :
    cupProduct f = DeRham.cupProduct f f (𝟙 S) (𝟙 S) (DeRham.pushforwardSquare f) := sorry

/-- The shifted cup product followed by a derived trace. -/
noncomputable def pairing (n : ℕ)
    (τ : (pushforward f)⟦(2 * (n : ℤ))⟧ ⟶
      𝟙_ (ModuleDerived.{u} (targetSite S))) :
    pushforward f ⊗ (pushforward f)⟦(2 * (n : ℤ))⟧ ⟶
      𝟙_ (ModuleDerived.{u} (targetSite S)) :=
  (((tensoringLeft (ModuleDerived.{u} (targetSite S))).obj
      (pushforward f)).commShiftIso (2 * (n : ℤ))).hom.app (pushforward f) ≫
    (cupProduct f)⟦(2 * (n : ℤ))⟧' ≫ τ

/-- The derived pairing is the tensor-shift comparison followed by shifted cup product and
the trace. -/
theorem pairing_eq (n : ℕ)
    (τ : (pushforward f)⟦(2 * (n : ℤ))⟧ ⟶
      𝟙_ (ModuleDerived.{u} (targetSite S))) :
    pairing f n τ =
      (((tensoringLeft (ModuleDerived.{u} (targetSite S))).obj
        (pushforward f)).commShiftIso (2 * (n : ℤ))).hom.app (pushforward f) ≫
      (cupProduct f)⟦(2 * (n : ℤ))⟧' ≫ τ := sorry

variable [MonoidalClosed (ModuleDerived.{u} (targetSite S))]
variable [BraidedCategory (ModuleDerived.{u} (targetSite S))]

/-- A derived trace is perfect when currying its whole-complex cup pairing gives an
isomorphism. -/
def IsPerfect (n : ℕ)
    (τ : (pushforward f)⟦(2 * (n : ℤ))⟧ ⟶
      𝟙_ (ModuleDerived.{u} (targetSite S))) : Prop :=
  RingedSite.Hom.ModuleDerived.IsPerfect (pushforward f) ∧
    IsIso (braidedHomEquiv (pushforward f) ((pushforward f)⟦(2 * (n : ℤ))⟧)
      (𝟙_ (ModuleDerived.{u} (targetSite S))) (pairing f n τ))

/-- Perfectness means that the pushed complex is perfect and the curried whole-complex
cup-trace pairing is invertible. -/
theorem isPerfect_iff (n : ℕ)
    (τ : (pushforward f)⟦(2 * (n : ℤ))⟧ ⟶
      𝟙_ (ModuleDerived.{u} (targetSite S))) :
    IsPerfect f n τ ↔
      RingedSite.Hom.ModuleDerived.IsPerfect (pushforward f) ∧
        IsIso (braidedHomEquiv (pushforward f) ((pushforward f)⟦(2 * (n : ℤ))⟧)
          (𝟙_ (ModuleDerived.{u} (targetSite S))) (pairing f n τ)) := sorry

end Pairing

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

/-- Under the relative Poincaré-duality hypotheses, multiplication by a global unit commutes
with the relative de Rham differential. -/
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
    DeRham.derivedComplex f ⟶ DeRham.derivedComplex f :=
  (moduleLocalization.{u} (sourceSite f)).map
    ((HomotopyCategory.quotient _ (up ℤ)).map
      (HomologicalComplex.extendMap (complexUnitAction f n h_nonempty a) embeddingUpNat))

variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{u} (cupHom f))
  (ModuleQis.{u} (sourceSite f))]

/-- The endomorphism of `Rf_*Ωᵈᴿ[X/S]` induced by multiplication by a global unit. -/
noncomputable def pushforwardUnitAction (n : ℕ) [CompactSpace S]
    [QuasiSeparatedSpace S] [IsProper f] [Smooth f]
    [Scheme.Hom.RelativeDimension f n]
    (h_nonempty : ∀ s : S, Nonempty (f.fiber s)) (a : Γ(X, ⊤)ˣ) :
    pushforward f ⟶ pushforward f :=
  (modulePushforwardDerived.{u} (cupHom f)).map
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
