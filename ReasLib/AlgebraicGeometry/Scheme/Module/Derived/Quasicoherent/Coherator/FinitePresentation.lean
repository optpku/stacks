/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Coherator
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Topology

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The quasicoherent coreflection on the source of a finite-presentation morphism whose target
is quasi-compact and quasi-separated. -/
noncomputable abbrev coheratorOfFinitePresentation {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [Scheme.Hom.FinitePresentation f] :
    RingedSpace.ModuleDerived X.toRingedSpace ⥤ Scheme.ModuleDerived.Quasicoherent X :=
  @Functor.rightAdjoint _ _ _ _ (Scheme.ModuleDerived.Quasicoherent.inclusion X)
    (@inclusionIsLeftAdjoint X
      (Scheme.Hom.compactSpace_of_finitePresentation f)
      (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))

end AlgebraicGeometry.Scheme.DerivedQCoh
