/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Abelian
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.HigherDirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Cech.Properties
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Abutment
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation

/-! # Relative Čech spectral sequence for quasi-coherent higher direct images -/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X Y : GroupoidsOver S}

/-- The first-page object `R^q (g ∘ f_p)_{QCoh,*} (f_p^* F)` of the relative
Čech quasi-coherent pushforward spectral sequence, as an object of
`QCoh 𝒴`. Here `f_p` is `Cech.proj f ⦋p⦌`. -/
noncomputable abbrev qcohRelativeCechPushforwardPageOne
    [AlgebraicStack X] [AlgebraicStack Y] (f : U ⟶ X) (g : X ⟶ Y)
    (F : QCoh X) (p q : ℕ)
    [AlgebraicStack (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌)]
    [AlgebraicStack.QuasiCompact
      (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g)]
    [AlgebraicStack.QuasiSeparated
      (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g)] :
    QCoh Y :=
  qCohHigherDirectImage (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g)
    ((QCoh.pullback (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌)).obj F) q

/-- Unfolding of `qcohRelativeCechPushforwardPageOne` as a quasi-coherent
higher direct image of `f_p^* F` along `g ∘ f_p`. -/
theorem qcohRelativeCechPushforwardPageOne_obj
    [AlgebraicStack X] [AlgebraicStack Y] (f : U ⟶ X) (g : X ⟶ Y)
    (F : QCoh X) (p q : ℕ)
    [AlgebraicStack (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌)]
    [AlgebraicStack.QuasiCompact
      (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g)]
    [AlgebraicStack.QuasiSeparated
      (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g)] :
    qcohRelativeCechPushforwardPageOne f g F p q =
      qCohHigherDirectImage (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g)
        ((QCoh.pullback (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌)).obj F) q :=
  rfl


/-- A surjective flat locally finitely presented quasi-compact quasi-separated
cover computes quasi-coherent higher direct images along a quasi-compact
quasi-separated morphism by a first-quadrant Čech spectral sequence. Its
`E₁`-page is `R^q (g ∘ f_p)_{QCoh,*} (f_p^* F)` and it converges to
`R^n g_{QCoh,*} F` in total degree `n`. -/
theorem exists_qcohRelativeCechPushforwardSpectralSequence
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    (f : U ⟶ X) (g : X ⟶ Y) (F : QCoh X)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f]
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    ∃ (E : CohomologicalSpectralSequenceNat (QCoh Y) 1)
      (pageOneIso : ∀ p q,
        (E.page 1 le_rfl).X (p, q) ≅
          qcohRelativeCechPushforwardPageOne f g F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ qCohHigherDirectImage g F n) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
