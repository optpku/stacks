/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Square
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RestrictToScheme
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TensorProduct
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative

/-!
# Étale characterizations of relative perfectness

Relative perfectness for flat, locally finitely presented morphisms of algebraic spaces
can be tested on étale scheme squares or by derived global sections on affine squares.
The scheme comparison is the right-derived étale-to-Zariski direct image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo

variable {S : Scheme.{u}}
/-- The scheme-level `V`-perfectness test of `E|_U` on an étale chart square, in the sense of
`Scheme.ModuleDerived.IsPerfectRelativeTo`. -/
def onEtaleSquare {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (sq : EtaleSquare f)
    [hFlat : AlgebraicGeometry.Flat sq.map.left]
    [hLFP : AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left]
    (E : ModuleDerived X) : Prop :=
  Scheme.ModuleDerived.IsPerfectRelativeTo sq.map.left
    ((DerivedQCoh.SchemeRestriction.derived sq.left.left).obj ((pullback sq.left.hom).obj E))

/-- The étale-square test unfolds to scheme-level relative perfectness of the restricted
complex on the source chart. -/
theorem onEtaleSquare_iff {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (sq : EtaleSquare f)
    [AlgebraicGeometry.Flat sq.map.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left]
    (E : ModuleDerived X) :
    onEtaleSquare sq E ↔
      Scheme.ModuleDerived.IsPerfectRelativeTo sq.map.left
        ((DerivedQCoh.SchemeRestriction.derived sq.left.left).obj
          ((pullback sq.left.hom).obj E)) := sorry

/-- The restricted complex is relatively perfect on every étale scheme square. -/
def everyEtaleSquare {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] (E : ModuleDerived X) : Prop :=
  ∀ (sq : EtaleSquare f) [AlgebraicGeometry.Flat sq.map.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left],
    onEtaleSquare sq E

/-- Testing every étale square is equivalent to relative perfectness on each such square. -/
theorem everyEtaleSquare_iff {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] (E : ModuleDerived X) :
    everyEtaleSquare f E ↔
      ∀ (sq : EtaleSquare f) [AlgebraicGeometry.Flat sq.map.left]
        [AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left],
        onEtaleSquare sq E := sorry

/-- Universal étale-square relative perfectness specializes to each étale square. -/
theorem everyEtaleSquare_spec {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] {E : ModuleDerived X}
    (h : everyEtaleSquare f E) (sq : EtaleSquare f)
    [AlgebraicGeometry.Flat sq.map.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left] :
    onEtaleSquare sq E := sorry

/-- There is an étale scheme square with surjective source chart on which the restricted complex is relatively perfect. -/
def existsSurjectiveEtaleSquare {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] (E : ModuleDerived X) :
    Prop :=
  ∃ (sq : EtaleSquare f) (hFlat : AlgebraicGeometry.Flat sq.map.left)
      (hLFP : AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left),
    Surjective sq.left.hom ∧ onEtaleSquare sq E (hFlat := hFlat) (hLFP := hLFP)

/-- Existence of a surjective étale test is equivalent to a surjective source chart with relatively perfect restriction. -/
theorem existsSurjectiveEtaleSquare_iff {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] (E : ModuleDerived X) :
    existsSurjectiveEtaleSquare f E ↔
      ∃ (sq : EtaleSquare f) (hFlat : AlgebraicGeometry.Flat sq.map.left)
          (hLFP : AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left),
        Surjective sq.left.hom ∧ onEtaleSquare sq E (hFlat := hFlat) (hLFP := hLFP) := sorry

/-- The `RΓ` test on an affine étale scheme square: derived global sections of `E|_U`
are `𝒪_Y(V)`-perfect. -/
def affineSectionsRelative {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (sq : EtaleSquare f)
    [IsAffine sq.left.left.left] [IsAffine sq.right.left.left]
    [AlgebraicGeometry.Flat sq.map.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left]
    (E : ModuleDerived X) : Prop :=
  @DerivedCategory.IsPerfectOver (Scheme.globalSectionsRing sq.right.left.left) _
    (Scheme.globalSectionsRing sq.left.left.left) _
    (Scheme.Hom.appTop sq.map.left).hom.toAlgebra
    ((RingedSpace.moduleDerivedGlobalSections
        sq.left.left.left.toRingedSpace).obj
      ((DerivedQCoh.SchemeRestriction.derived sq.left.left).obj
        ((pullback sq.left.hom).obj E)))

/-- The affine `RΓ` test unfolds to algebra-level relative perfectness of `RΓ(U, E)`
over `𝒪_Y(V)`. -/
theorem affineSectionsRelative_iff {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} (sq : EtaleSquare f)
    [IsAffine sq.left.left.left]
    [IsAffine sq.right.left.left] [AlgebraicGeometry.Flat sq.map.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left]
    (E : ModuleDerived X) :
    affineSectionsRelative sq E ↔
      @DerivedCategory.IsPerfectOver (Scheme.globalSectionsRing sq.right.left.left) _
        (Scheme.globalSectionsRing sq.left.left.left) _
        (Scheme.Hom.appTop sq.map.left).hom.toAlgebra
        ((RingedSpace.moduleDerivedGlobalSections
            sq.left.left.left.toRingedSpace).obj
          ((DerivedQCoh.SchemeRestriction.derived sq.left.left).obj
            ((pullback sq.left.hom).obj E))) := sorry

/-- Derived global sections are perfect over the target chart ring on every affine étale square. -/
def everyAffineSections {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] (E : ModuleDerived X) : Prop :=
  ∀ (sq : EtaleSquare f) [IsAffine sq.left.left.left]
    [IsAffine sq.right.left.left] [AlgebraicGeometry.Flat sq.map.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left],
    affineSectionsRelative sq E

/-- The universal affine test is equivalent to relative perfectness of derived sections on each affine étale square. -/
theorem everyAffineSections_iff {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] (E : ModuleDerived X) :
    everyAffineSections f E ↔
      ∀ (sq : EtaleSquare f) [IsAffine sq.left.left.left]
        [IsAffine sq.right.left.left] [AlgebraicGeometry.Flat sq.map.left]
        [AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left],
        affineSectionsRelative sq E := sorry

/-- Universal affine relative perfectness specializes to derived sections on each affine étale square. -/
theorem everyAffineSections_spec {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] {E : ModuleDerived X}
    (h : everyAffineSections f E) (sq : EtaleSquare f)
    [IsAffine sq.left.left.left] [IsAffine sq.right.left.left]
    [AlgebraicGeometry.Flat sq.map.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left] :
    affineSectionsRelative sq E := sorry

/-- For a quasi-coherent derived complex, testing every étale square is equivalent to testing one square with surjective source chart. -/
theorem everyEtaleSquare_iff_existsSurjectiveEtaleSquare
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f]
    {E : ModuleDerived X} (hE : derivedQuasiCoherentModuleProperty X E) :
    everyEtaleSquare f E ↔ existsSurjectiveEtaleSquare f E := sorry

/-- For a quasi-coherent derived complex, testing relative perfectness on all étale squares is equivalent to testing derived sections on affine étale squares. -/
theorem everyEtaleSquare_iff_everyAffineSections
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f]
    {E : ModuleDerived X} (hE : derivedQuasiCoherentModuleProperty X E) :
    everyEtaleSquare f E ↔ everyAffineSections f E := sorry

/-- `Y`-perfectness of `E` is equivalent to `V`-perfectness of `E|_U` on every étale
scheme square over `f`. -/
theorem iff_everyEtaleSquare {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] {E : ModuleDerived X}
    (hE : derivedQuasiCoherentModuleProperty X E) :
    IsPerfectRelativeTo f E ↔ everyEtaleSquare f E := sorry

/-- `Y`-perfectness of `E` is equivalent to `V`-perfectness of `E|_U` on some étale
scheme square over `f` with `U ⟶ X` surjective. -/
theorem iff_existsSurjectiveEtaleSquare {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] {E : ModuleDerived X}
    (hE : derivedQuasiCoherentModuleProperty X E) :
    IsPerfectRelativeTo f E ↔ existsSurjectiveEtaleSquare f E := sorry

/-- `Y`-perfectness of `E` is equivalent to `𝒪_Y(V)`-perfectness of `RΓ(U, E)` on every
affine étale scheme square over `f`. -/
theorem iff_everyAffineSections {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] {E : ModuleDerived X}
    (hE : derivedQuasiCoherentModuleProperty X E) :
    IsPerfectRelativeTo f E ↔ everyAffineSections f E := sorry

/-- For a flat, locally finitely presented morphism and a quasi-coherent derived complex,
intrinsic relative perfectness, all étale-square tests, one surjective étale-square test,
and all affine derived-sections tests are equivalent. -/
theorem tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] {E : ModuleDerived X}
    (hE : derivedQuasiCoherentModuleProperty X E) :
    List.TFAE [IsPerfectRelativeTo f E, IsPerfectRelativeTo.everyEtaleSquare f E,
      IsPerfectRelativeTo.existsSurjectiveEtaleSquare f E,
      IsPerfectRelativeTo.everyAffineSections f E] := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo
