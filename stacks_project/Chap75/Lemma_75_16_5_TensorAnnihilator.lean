module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.Topology.Sets.Closeds
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_20_1_Sheaf
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_5_2_EtaleLocal
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap81.Lemma_81_10_10_SupportedOn

/-!
# Tensor annihilators of supported morphisms

On a quasi-compact quasi-separated algebraic space, a morphism in `D_QCoh(𝒪_X)` from a
perfect complex, or from a pseudo-coherent complex to a bounded-below complex, with
target supported on a closed subset `T` with quasi-compact complement, is annihilated
after derived tensoring by a perfect complex whose map to the tensor unit is invertible
on that complement.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory DerivedCategory.TStructure TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn

/-- A morphism from a perfect complex, or from a pseudo-coherent complex to a bounded-below
complex, with target supported on a closed subset is annihilated after tensoring by a perfect
complex whose map to the tensor unit is invertible away from that subset. -/
@[stacks 0AEE]
theorem existsTensorAnnihilator {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [MonoidalCategory (ModuleDerived X)] (T : Closeds (Points X))
    (hT : QuasiCompact (OpenSubspace.ofOpensι T.compl)) (P : DerivedQCoh X)
    (E : SupportedOn X (T : Set (Points X)))
    (α : P ⟶ (inclusion X (T : Set (Points X))).obj E)
    (h : ModuleDerived.IsPerfect P.obj ∨
      (IsPseudoCoherent X P.obj ∧
        (t.plus : ObjectProperty (ModuleDerived X)) E.obj)) :
    ∃ (I : ModuleDerived X) (i : I ⟶ 𝟙_ (ModuleDerived X)),
      ModuleDerived.IsPerfect I ∧
        (i ⊗ₘ 𝟙 P.obj) ≫ (λ_ P.obj).hom ≫
          (DerivedQCoh.inclusion X).map α = 0 ∧
        IsIso ((ModuleDerived.pullback (OpenSubspace.ofOpensι T.compl)).map i) :=
  sorry

/-- A morphism from a perfect complex to a complex supported on a closed subset is annihilated
after tensoring by a perfect complex whose map to the tensor unit is invertible away from that
subset. -/
theorem existsTensorAnnihilator_of_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [MonoidalCategory (ModuleDerived X)] (T : Closeds (Points X))
    (hT : QuasiCompact (OpenSubspace.ofOpensι T.compl)) (P : DerivedQCoh X)
    (E : SupportedOn X (T : Set (Points X)))
    (α : P ⟶ (inclusion X (T : Set (Points X))).obj E)
    (hP : ModuleDerived.IsPerfect P.obj) :
    ∃ (I : ModuleDerived X) (i : I ⟶ 𝟙_ (ModuleDerived X)),
      ModuleDerived.IsPerfect I ∧
        (i ⊗ₘ 𝟙 P.obj) ≫ (λ_ P.obj).hom ≫
          (DerivedQCoh.inclusion X).map α = 0 ∧
        IsIso ((ModuleDerived.pullback (OpenSubspace.ofOpensι T.compl)).map i) :=
  sorry

/-- A morphism from a pseudo-coherent complex to a bounded-below complex supported on a closed
subset is annihilated after tensoring by a perfect complex whose map to the tensor unit is
invertible away from that subset. -/
theorem existsTensorAnnihilator_of_isPseudoCoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [MonoidalCategory (ModuleDerived X)] (T : Closeds (Points X))
    (hT : QuasiCompact (OpenSubspace.ofOpensι T.compl)) (P : DerivedQCoh X)
    (E : SupportedOn X (T : Set (Points X)))
    (α : P ⟶ (inclusion X (T : Set (Points X))).obj E)
    (hP : IsPseudoCoherent X P.obj)
    (hE : (t.plus : ObjectProperty (ModuleDerived X)) E.obj) :
    ∃ (I : ModuleDerived X) (i : I ⟶ 𝟙_ (ModuleDerived X)),
      ModuleDerived.IsPerfect I ∧
        (i ⊗ₘ 𝟙 P.obj) ≫ (λ_ P.obj).hom ≫
          (DerivedQCoh.inclusion X).map α = 0 ∧
        IsIso ((ModuleDerived.pullback (OpenSubspace.ofOpensι T.compl)).map i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn
