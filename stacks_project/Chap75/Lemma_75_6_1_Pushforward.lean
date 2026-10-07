module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Lemma_67_4_4_Pullback
public import stacks_project.Chap67.Lemma_67_8_4_QuasiCompact
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward

/-!
# Restricted derived pushforward on algebraic spaces

Ambient derived pushforward along a quasi-compact, quasi-separated morphism
restricts to the full subcategory of complexes with quasi-coherent cohomology,
and has a uniform cohomological bound after arbitrary base change when the
target is quasi-compact.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

namespace pushforward

/-- Derived pushforward along a quasi-compact, quasi-separated morphism of algebraic
spaces preserves derived modules with quasi-coherent cohomology. -/
theorem mapsTo (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    derivedQuasiCoherentModuleProperty X ≤
      (derivedQuasiCoherentModuleProperty Y).inverseImage
        (Modules.pushforwardDerived f) :=
  sorry

end pushforward

/-- Ambient derived pushforward `Rf_*`, restricted to complexes with quasi-coherent
cohomology. -/
noncomputable def pushforward (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    DerivedQCoh X ⥤ DerivedQCoh Y :=
  (derivedQuasiCoherentModuleProperty Y).lift
    ((derivedQuasiCoherentModuleProperty X).ι ⋙ Modules.pushforwardDerived f)
    (fun E ↦ pushforward.mapsTo f E.obj E.property)

namespace pushforward

/-- Forgetting the restricted ambient pushforward recovers ambient derived pushforward. -/
noncomputable def inclusionIso (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    pushforward f ⋙ (derivedQuasiCoherentModuleProperty Y).ι ≅
      (derivedQuasiCoherentModuleProperty X).ι ⋙ Modules.pushforwardDerived f :=
  (derivedQuasiCoherentModuleProperty Y).liftCompιIso
    ((derivedQuasiCoherentModuleProperty X).ι ⋙ Modules.pushforwardDerived f)
    (fun E ↦ mapsTo f E.obj E.property)

/-- Over a quasi-compact algebraic space, derived pushforward along a quasi-compact and
quasi-separated morphism has a uniform upper cohomological bound on complexes whose
positive cohomology vanishes. -/
theorem uniformUpperBound (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsQuasiCompact Y] :
    ∃ N : ℤ, ∀ E : DerivedQCoh X,
      E.obj.IsLE 0 → ((pushforward f).obj E).obj.IsLE (N - 1) :=
  sorry

/-- The upper cohomological bound for derived pushforward along a quasi-compact and
quasi-separated morphism can be chosen uniformly after every base change. -/
theorem baseChangeUpperBound (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsQuasiCompact Y] :
    ∃ N : ℤ, ∀ ⦃Y' : AlgebraicSpace S⦄ (g : Y' ⟶ Y)
      (E : DerivedQCoh (pullback f g)),
      E.obj.IsLE 0 →
        ((pushforward (pullback.snd f g)).obj E).obj.IsLE (N - 1) :=
  sorry

end pushforward

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
