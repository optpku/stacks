module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTransport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.CategoryTheory.MonoidalCategory.TensorPower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.VanishingH1
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample

/-! # A cohomological criterion for representability and ampleness -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A Noetherian algebraic space with an invertible module such that every coherent module
has a positive tensor twist with vanishing first cohomology is a scheme, and the invertible
module is ample on every representing scheme. -/
theorem isScheme_and_isAmpleObject_of_coherent_h1_twist_zero {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsNoetherian X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    (L : X.Modules) [isInvertibleObject L]
    (hH1 : ∀ (F : Modules X) [F.IsCoherent],
      ∃ n : ℕ, 0 < n ∧ IsZero (cohomology X (F ⊗ tensorPower L n) 1)) :
    IsScheme X ∧ ∀ {T : Over S} (e : X ≅ ofOver T),
      Scheme.Modules.isAmpleObject (Modules.toSchemeModule e L) :=
  sorry

/-- For an invertible module on an algebraic space proper over a Noetherian ring, being a
scheme with an ample module is equivalent both to eventual vanishing of all positive-degree
cohomology of every coherent module after twisting and to existence of a positive twist with
vanishing first cohomology for every coherent module. -/
@[stacks 0GFA]
theorem isSchemeAndAmple_tfae {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper f]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    (L : X.Modules) [isInvertibleObject L] :
    List.TFAE
      [ Modules.isSchemeAndAmple L,
        ∀ F : X.Modules, F.IsCoherent →
          ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ p : ℕ, 0 < p →
            IsZero (cohomology X (F ⊗ tensorPower L n) p),
        ∀ F : X.Modules, F.IsCoherent →
          ∃ n : ℕ, 0 < n ∧
            IsZero (cohomology X (F ⊗ tensorPower L n) 1) ] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
