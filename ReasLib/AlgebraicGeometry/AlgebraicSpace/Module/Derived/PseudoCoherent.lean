module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.StrictlyPerfect
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Homology.Additive

/-!
# Pseudo-coherent derived modules on algebraic spaces

Pseudo-coherence is expressed by local strictly perfect approximations on the small étale
site, with coefficients in the original universe. These approximations give quasi-coherent
cohomology above the approximation degree and in every degree for pseudo-coherent objects.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace CochainComplex

/-- A complex of `𝒪_X`-modules is `m`-pseudo-coherent if locally it admits a map from a
strictly perfect complex inducing cohomology isomorphisms above `m` and an epimorphism in
degree `m`. -/
def IsMPseudoCoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E : _root_.CochainComplex (Modules X) ℤ) (m : ℤ) : Prop :=
  ∀ U : smallEtaleSite X, ∃ T : (smallEtaleTopology X).Cover U, ∀ I : T.Arrow,
    ∃ E' : _root_.CochainComplex
        (SheafOfModules.{u} ((structureSheaf X).over I.Y)) ℤ,
      SheafOfModules.CochainComplex.IsStrictlyPerfect E' ∧
        ∃ alpha :
            E' ⟶ ((SheafOfModules.Localization.restriction (structureSheaf X) I.Y).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E,
          (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap alpha j)) ∧
            Epi (HomologicalComplex.homologyMap alpha m)

/-- A complex of `𝒪_X`-modules is pseudo-coherent if it is `m`-pseudo-coherent for every
integer `m`. -/
def IsPseudoCoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E : _root_.CochainComplex (Modules X) ℤ) : Prop :=
  ∀ m : ℤ, IsMPseudoCoherent E m

end CochainComplex

/-- A derived `𝒪_X`-module is `m`-pseudo-coherent when it has an `m`-pseudo-coherent
complex representative. -/
def IsMPseudoCoherent {S : Scheme.{u}} (X : AlgebraicSpace S)
    (E : ModuleDerived X) (m : ℤ) : Prop :=
  ∃ F : _root_.CochainComplex (Modules X) ℤ, ∃ _ : E ≅ DerivedCategory.Q.obj F,
    CochainComplex.IsMPseudoCoherent F m

/-- A derived `𝒪_X`-module is pseudo-coherent when it has a pseudo-coherent complex
representative. -/
def IsPseudoCoherent {S : Scheme.{u}} (X : AlgebraicSpace S)
    (E : ModuleDerived X) : Prop :=
  ∃ F : _root_.CochainComplex (Modules X) ℤ, ∃ _ : E ≅ DerivedCategory.Q.obj F,
    CochainComplex.IsPseudoCoherent F

/-- A derived `𝒪_X`-module on an algebraic space is pseudo-coherent if and only if it is
`m`-pseudo-coherent for every integer `m`. -/
theorem isPseudoCoherent_iff_forall_isMPseudoCoherent
    {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X} :
    IsPseudoCoherent X E ↔ ∀ m : ℤ, IsMPseudoCoherent X E m := sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.PseudoCoherent

/-- The cohomology sheaves of an `m`-pseudo-coherent derived module in degrees strictly above
`m` are quasi-coherent. -/
theorem higherCohomology_isQuasicoherent
    {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X} {m i : ℤ}
    (hE : IsMPseudoCoherent X E m) (hi : m < i) :
    ((DerivedCategory.homologyFunctor (Modules X) i).obj E).IsQuasicoherent := sorry

/-- A pseudo-coherent derived `𝒪_X`-module on an algebraic space lies in `D_QCoh(𝒪_X)`. -/
theorem derivedQuasiCoherentModuleProperty
    {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X}
    (hE : IsPseudoCoherent X E) :
    AlgebraicGeometry.AlgebraicSpace.derivedQuasiCoherentModuleProperty X E := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.PseudoCoherent
