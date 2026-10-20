module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.StrictlyPerfect
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Localization
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh

/-!
# Pseudo-coherent derived modules on algebraic spaces

Typed compatibility checks for the pseudo-coherence predicates and their cohomology results.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.CochainComplex.IsMPseudoCoherent :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
    _root_.CochainComplex (Modules X) ℤ → ℤ → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.CochainComplex.IsPseudoCoherent :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
    _root_.CochainComplex (Modules X) ℤ → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.IsMPseudoCoherent :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), ModuleDerived X → ℤ → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.IsPseudoCoherent :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), ModuleDerived X → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isPseudoCoherent_iff_forall_isMPseudoCoherent :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X},
    IsPseudoCoherent X E ↔ ∀ m : ℤ, IsMPseudoCoherent X E m)

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.PseudoCoherent.higherCohomology_isQuasicoherent :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X} {m i : ℤ},
    IsMPseudoCoherent X E m → m < i →
      ((DerivedCategory.homologyFunctor (Modules X) i).obj E).IsQuasicoherent)

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.PseudoCoherent.derivedQuasiCoherentModuleProperty :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X},
    IsPseudoCoherent X E → derivedQuasiCoherentModuleProperty X E)
