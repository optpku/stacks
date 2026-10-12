/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import stacks_project.Chap66.Definition_66_18_9_Square
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_20_7_BaseChange

/-!
# Étale characterizations of relative `m`-pseudo-coherence

On a locally finite type morphism of algebraic spaces, relative `m`-pseudo-coherence
of an object of `D_QCoh(𝒪_X)` is tested on étale scheme squares by the affine-open
`RΓ` criterion, on some square with surjective source chart, and on affine étale
squares by derived global sections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsMPseudoCoherentOver

/-- The scheme-level relative `m`-pseudo-coherence test of `E|_U` against `V`, encoded
by the affine-open `RΓ` criterion on the étale chart square. -/
def onEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (sq : EtaleSquare f)
    [AlgebraicGeometry.LocallyOfFiniteType sq.map.left]
    (E : ModuleDerived X) (m : ℤ) : Prop :=
  ∀ (V : sq.right.left.left.affineOpens) (U : sq.left.left.left.affineOpens)
    (e : (U : sq.left.left.left.Opens) ≤
      sq.map.left ⁻¹ᵁ (V : sq.right.left.left.Opens)),
    @DerivedCategory.IsMPseudoCoherentRelativeTo
      Γ(sq.right.left.left, (V : sq.right.left.left.Opens)) _
      Γ(sq.left.left.left, (U : sq.left.left.left.Opens)) _
      (Scheme.Hom.sectionsAlgebra sq.map.left V U e)
      (sq.map.left.finiteType_appLE V.property U.property e)
      ((RingedSpace.moduleDerivedSectionsAtOpen
          sq.left.left.left.toRingedSpace U).obj
        ((restrictToEtaleChart sq.left).obj E)) m

/-- The étale-square test unfolds to relative `m`-pseudo-coherence of derived sections
on every compatible pair of affine opens of the chart schemes. -/
theorem onEtaleSquare_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (sq : EtaleSquare f)
    [AlgebraicGeometry.LocallyOfFiniteType sq.map.left]
    (E : ModuleDerived X) (m : ℤ) :
    onEtaleSquare sq E m ↔
      ∀ (V : sq.right.left.left.affineOpens) (U : sq.left.left.left.affineOpens)
        (e : (U : sq.left.left.left.Opens) ≤
          sq.map.left ⁻¹ᵁ (V : sq.right.left.left.Opens)),
        @DerivedCategory.IsMPseudoCoherentRelativeTo
          Γ(sq.right.left.left, (V : sq.right.left.left.Opens)) _
          Γ(sq.left.left.left, (U : sq.left.left.left.Opens)) _
          (Scheme.Hom.sectionsAlgebra sq.map.left V U e)
          (sq.map.left.finiteType_appLE V.property U.property e)
          ((RingedSpace.moduleDerivedSectionsAtOpen
              sq.left.left.left.toRingedSpace U).obj
            ((restrictToEtaleChart sq.left).obj E)) m :=
  sorry

/-- Clause (1): `E|_U` is `m`-pseudo-coherent relative to `V` on every étale scheme
square over `f`. -/
def everyEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (E : ModuleDerived X) (m : ℤ) : Prop :=
  ∀ (sq : EtaleSquare f) [AlgebraicGeometry.LocallyOfFiniteType sq.map.left],
    onEtaleSquare sq E m

/-- Clause (1) unfolds to the affine-open `RΓ` test on every étale scheme square. -/
theorem everyEtaleSquare_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (E : ModuleDerived X) (m : ℤ) :
    everyEtaleSquare f E m ↔
      ∀ (sq : EtaleSquare f)
        [AlgebraicGeometry.LocallyOfFiniteType sq.map.left],
        onEtaleSquare sq E m :=
  sorry

/-- On any étale scheme square over `f`, clause (1) yields relative `m`-pseudo-coherence
of `E|_U` with respect to `V`. -/
theorem everyEtaleSquare_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {E : ModuleDerived X} {m : ℤ}
    (h : everyEtaleSquare f E m) (sq : EtaleSquare f)
    [AlgebraicGeometry.LocallyOfFiniteType sq.map.left] :
    onEtaleSquare sq E m :=
  sorry

/-- Clause (2): `E|_U` is `m`-pseudo-coherent relative to `V` on some étale scheme
square over `f` with `U ⟶ X` surjective. -/
def existsSurjectiveEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (E : ModuleDerived X) (m : ℤ) : Prop :=
  ∃ (sq : EtaleSquare f)
      (h_lft : AlgebraicGeometry.LocallyOfFiniteType sq.map.left),
    Surjective sq.left.hom ∧ @onEtaleSquare _ _ _ _ sq h_lft E m

/-- Clause (2) unfolds to existence of an étale scheme square with surjective source
chart on which the affine-open `RΓ` test holds. -/
theorem existsSurjectiveEtaleSquare_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (E : ModuleDerived X) (m : ℤ) :
    existsSurjectiveEtaleSquare f E m ↔
      ∃ (sq : EtaleSquare f)
          (h_lft : AlgebraicGeometry.LocallyOfFiniteType sq.map.left),
        Surjective sq.left.hom ∧ @onEtaleSquare _ _ _ _ sq h_lft E m :=
  sorry

/-- The `RΓ` test on an affine étale scheme square: derived global sections of `E|_U`
are `m`-pseudo-coherent relative to `𝒪_Y(V)` as a complex of `𝒪_X(U)`-modules. -/
def affineSectionsRelative {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (sq : EtaleSquare f) [IsAffine sq.left.left.left] [IsAffine sq.right.left.left]
    [AlgebraicGeometry.LocallyOfFiniteType sq.map.left] (E : ModuleDerived X)
    (m : ℤ) : Prop :=
  ∃ hFT : (Scheme.Hom.appTop sq.map.left).hom.FiniteType,
    @DerivedCategory.IsMPseudoCoherentRelativeTo
      (Scheme.globalSectionsRing sq.right.left.left) _
      (Scheme.globalSectionsRing sq.left.left.left) _
      (Scheme.Hom.appTop sq.map.left).hom.toAlgebra hFT
      ((RingedSpace.moduleDerivedGlobalSections
          sq.left.left.left.toRingedSpace).obj
        ((restrictToEtaleChart sq.left).obj E)) m

/-- The affine `RΓ` test unfolds to finite type of the global-sections algebra together
with derived relative `m`-pseudo-coherence of `RΓ(U, E)` over `𝒪_Y(V)`. -/
theorem affineSectionsRelative_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} (sq : EtaleSquare f) [IsAffine sq.left.left.left]
    [IsAffine sq.right.left.left]
    [AlgebraicGeometry.LocallyOfFiniteType sq.map.left] (E : ModuleDerived X)
    (m : ℤ) :
    affineSectionsRelative sq E m ↔
      ∃ hFT : (Scheme.Hom.appTop sq.map.left).hom.FiniteType,
        @DerivedCategory.IsMPseudoCoherentRelativeTo
          (Scheme.globalSectionsRing sq.right.left.left) _
          (Scheme.globalSectionsRing sq.left.left.left) _
          (Scheme.Hom.appTop sq.map.left).hom.toAlgebra hFT
          ((RingedSpace.moduleDerivedGlobalSections
              sq.left.left.left.toRingedSpace).obj
            ((restrictToEtaleChart sq.left).obj E)) m :=
  sorry

/-- Clause (3): on every affine étale scheme square over `f`, the complex `RΓ(U, E)`
of `𝒪_X(U)`-modules is `m`-pseudo-coherent relative to `𝒪_Y(V)`. -/
def everyAffineSections {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (E : ModuleDerived X) (m : ℤ) : Prop :=
  ∀ (sq : EtaleSquare f) [IsAffine sq.left.left.left]
    [IsAffine sq.right.left.left]
    [AlgebraicGeometry.LocallyOfFiniteType sq.map.left],
    affineSectionsRelative sq E m

/-- Clause (3) unfolds to the affine `RΓ` test on every affine étale scheme square. -/
theorem everyAffineSections_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (E : ModuleDerived X) (m : ℤ) :
    everyAffineSections f E m ↔
      ∀ (sq : EtaleSquare f) [IsAffine sq.left.left.left]
        [IsAffine sq.right.left.left]
        [AlgebraicGeometry.LocallyOfFiniteType sq.map.left],
        affineSectionsRelative sq E m :=
  sorry

/-- On any affine étale scheme square over `f`, clause (3) yields the `RΓ` relative
`m`-pseudo-coherence test. -/
theorem everyAffineSections_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {E : ModuleDerived X} {m : ℤ}
    (h : everyAffineSections f E m) (sq : EtaleSquare f)
    [IsAffine sq.left.left.left] [IsAffine sq.right.left.left]
    [AlgebraicGeometry.LocallyOfFiniteType sq.map.left] :
    affineSectionsRelative sq E m :=
  sorry

/-- Clauses (1) and (2) are equivalent for `E` in `D_QCoh(𝒪_X)`. -/
theorem everyEtaleSquare_iff_existsSurjectiveEtaleSquare {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {E : ModuleDerived X} (hE : derivedQuasiCoherentModuleProperty X E) (m : ℤ) :
    everyEtaleSquare f E m ↔ existsSurjectiveEtaleSquare f E m :=
  sorry

/-- Clauses (1) and (3) are equivalent for `E` in `D_QCoh(𝒪_X)`. -/
theorem everyEtaleSquare_iff_everyAffineSections {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {E : ModuleDerived X} (hE : derivedQuasiCoherentModuleProperty X E) (m : ℤ) :
    everyEtaleSquare f E m ↔ everyAffineSections f E m :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsMPseudoCoherentOver
