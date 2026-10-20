/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor.Unit

/-!
# Tensor annihilators of supported morphisms

On a quasi-compact quasi-separated algebraic space, a morphism in `D_QCoh(𝒪_X)` from a
perfect complex, or from a pseudo-coherent complex to a bounded-below complex, with
target supported on a closed subset `T` with quasi-compact complement, is annihilated
after derived tensoring by a perfect complex whose map to the degree-zero structure sheaf is invertible
on that complement.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open DerivedCategory.TStructure TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn

/-- A morphism from a perfect complex, or from a pseudo-coherent complex to a bounded-below
complex, with target supported on a closed subset is annihilated after tensoring by a perfect
complex whose map to the degree-zero structure sheaf is invertible away from that subset. -/
@[stacks 0AEE]
theorem existsTensorAnnihilator {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (T : Closeds (Points X))
    (hT : QuasiCompact ((OpenSubspace.fromOpens T.compl).ι)) (P : DerivedQCoh X)
    (E : SupportedOn X (T : Set (Points X)))
    (α : P ⟶ (inclusion X (T : Set (Points X))).obj E)
    (h : ModuleDerived.IsPerfect P.obj ∨
      (IsPseudoCoherent X P.obj ∧
        (t.plus : ObjectProperty (ModuleDerived X)) E.obj)) :
    ∃ (I : ModuleDerived X) (i : I ⟶ (DerivedQCoh.structureSheaf X).obj),
      ModuleDerived.IsPerfect I ∧
        ((ModuleDerived.tensorBifunctor X).map (Prod.mkHom i (𝟙 P.obj))) ≫
          ModuleDerived.tensorLeftUnitor P.obj ≫
          (DerivedQCoh.inclusion X).map α = 0 ∧
        IsIso ((ModuleDerived.pullback ((OpenSubspace.fromOpens T.compl).ι)).map i) :=
  sorry

/-- A morphism from a perfect complex to a complex supported on a closed subset is annihilated
after tensoring by a perfect complex whose map to the degree-zero structure sheaf is invertible away from that
subset. -/
theorem existsTensorAnnihilator_of_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (T : Closeds (Points X))
    (hT : QuasiCompact ((OpenSubspace.fromOpens T.compl).ι)) (P : DerivedQCoh X)
    (E : SupportedOn X (T : Set (Points X)))
    (α : P ⟶ (inclusion X (T : Set (Points X))).obj E)
    (hP : ModuleDerived.IsPerfect P.obj) :
    ∃ (I : ModuleDerived X) (i : I ⟶ (DerivedQCoh.structureSheaf X).obj),
      ModuleDerived.IsPerfect I ∧
        ((ModuleDerived.tensorBifunctor X).map (Prod.mkHom i (𝟙 P.obj))) ≫
          ModuleDerived.tensorLeftUnitor P.obj ≫
          (DerivedQCoh.inclusion X).map α = 0 ∧
        IsIso ((ModuleDerived.pullback ((OpenSubspace.fromOpens T.compl).ι)).map i) :=
  existsTensorAnnihilator T hT P E α (Or.inl hP)

/-- A morphism from a pseudo-coherent complex to a bounded-below complex supported on a closed
subset is annihilated after tensoring by a perfect complex whose map to the degree-zero structure sheaf is
invertible away from that subset. -/
theorem existsTensorAnnihilator_of_isPseudoCoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (T : Closeds (Points X))
    (hT : QuasiCompact ((OpenSubspace.fromOpens T.compl).ι)) (P : DerivedQCoh X)
    (E : SupportedOn X (T : Set (Points X)))
    (α : P ⟶ (inclusion X (T : Set (Points X))).obj E)
    (hP : IsPseudoCoherent X P.obj)
    (hE : (t.plus : ObjectProperty (ModuleDerived X)) E.obj) :
    ∃ (I : ModuleDerived X) (i : I ⟶ (DerivedQCoh.structureSheaf X).obj),
      ModuleDerived.IsPerfect I ∧
        ((ModuleDerived.tensorBifunctor X).map (Prod.mkHom i (𝟙 P.obj))) ≫
          ModuleDerived.tensorLeftUnitor P.obj ≫
          (DerivedQCoh.inclusion X).map α = 0 ∧
        IsIso ((ModuleDerived.pullback ((OpenSubspace.fromOpens T.compl).ι)).map i) :=
  existsTensorAnnihilator T hT P E α (Or.inr ⟨hP, hE⟩)

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn
