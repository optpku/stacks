module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import ReasLib.CategoryTheory.Abelian.SerreQuotient
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Equivalence

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh.OpenRestriction

/-- Restriction of quasicoherent modules to an open subscheme is exact. -/
theorem pullbackIsExact {X : Scheme.{u}} (U : X.Opens) :
    exactFunctor (Scheme.QCoh X) (Scheme.QCoh U.toScheme)
      (Scheme.QCoh.pullback U.ι) := sorry

/-- The exact functor obtained by restricting quasicoherent modules to an open subscheme. -/
noncomputable def functor {X : Scheme.{u}} (U : X.Opens) :
    Scheme.QCoh X ⥤ₑ Scheme.QCoh U.toScheme :=
  ⟨Scheme.QCoh.pullback U.ι, pullbackIsExact U⟩

/-- The underlying functor of restriction to an open subscheme. -/
theorem functor_obj {X : Scheme.{u}} (U : X.Opens) :
    (functor U).obj = Scheme.QCoh.pullback U.ι := sorry

/-- The Serre class of quasicoherent modules whose restriction to the open subscheme vanishes. -/
abbrev kernel {X : Scheme.{u}} (U : X.Opens) :
    ObjectProperty (Scheme.QCoh X) := (functor U).obj.kernel

/-- A quasicoherent module restricts to zero exactly when its support lies in the closed complement. -/
theorem mem_kernel_iff {X : Scheme.{u}} (U : X.Opens) (F : Scheme.QCoh X) :
    kernel U F ↔ Scheme.Modules.moduleSupport F.obj ⊆ (U : Set X)ᶜ := sorry

/-- The functor induced by restriction on the Serre localization by its kernel. -/
noncomputable def quotientFunctor {X : Scheme.{u}} (U : X.Opens) :
    (kernel U).isoModSerre.Localization ⥤ Scheme.QCoh U.toScheme :=
  ObjectProperty.SerreClassLocalization.inducedFunctor
    (kernel U) (functor U) (le_rfl)

/-- The induced functor composed with the canonical quotient is restriction to the open subscheme. -/
noncomputable def quotientFunctorCompQuotientIso {X : Scheme.{u}} (U : X.Opens) :
    (kernel U).isoModSerre.Q ⋙ quotientFunctor U ≅ (functor U).obj :=
  Localization.fac (functor U).obj
    (((kernel U).isoModSerre_isInvertedBy_iff (functor U).obj).2 (le_rfl))
    (kernel U).isoModSerre.Q

/-- For a quasi-compact, quasi-separated scheme and a quasi-compact open subscheme,
restriction induces an equivalence from the Serre localization by modules supported on the
closed complement to quasicoherent modules on the open subscheme. -/
instance quotientFunctorIsEquivalence
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) [AlgebraicGeometry.QuasiCompact U.ι] :
    (quotientFunctor U).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.QCoh.OpenRestriction
