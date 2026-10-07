module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative
public import stacks_project.Chap66.Definition_66_18_9_Square
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap76.Lemma_76_52_4_Relative

/-!
# Étale characterizations of relative perfectness

On a flat, locally finitely presented morphism of algebraic spaces, `Y`-perfectness of
an object of `D_QCoh(𝒪_X)` is tested on étale scheme squares by scheme-level
`V`-perfectness of `E|_U`, on some square with surjective source chart, and on affine
étale squares by `𝒪_Y(V)`-perfectness of derived global sections.

The restriction `E|_U` is derived pullback to the source chart composed with
`restrictToSchemeDerived`, transported to the underlying ringed space. This is the
restriction available in the same import tree as `IsPerfectRelativeTo`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo

/-- The scheme-level `V`-perfectness test of `E|_U` on an étale chart square, in the sense of
`Scheme.ModuleDerived.IsPerfectRelativeTo`. -/
def onEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (sq : EtaleSquare f) [AlgebraicGeometry.Flat sq.map.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left]
    (E : ModuleDerived X) : Prop :=
  Scheme.ModuleDerived.IsPerfectRelativeTo sq.map.left
    (Eq.mp (derivedCategory_modules_eq_ringedSpace sq.left.left.left)
      ((restrictToSchemeDerived sq.left.left).obj ((pullback sq.left.hom).obj E)))

/-- The étale-square test unfolds to scheme-level relative perfectness of the restricted
complex on the source chart. -/
theorem onEtaleSquare_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (sq : EtaleSquare f) [AlgebraicGeometry.Flat sq.map.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left]
    (E : ModuleDerived X) :
    onEtaleSquare sq E ↔
      Scheme.ModuleDerived.IsPerfectRelativeTo sq.map.left
        (Eq.mp (derivedCategory_modules_eq_ringedSpace sq.left.left.left)
          ((restrictToSchemeDerived sq.left.left).obj
            ((pullback sq.left.hom).obj E))) :=
  sorry

/-- Clause (2): `E|_U` is `V`-perfect on every étale scheme square over `f`. -/
def everyEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] (E : ModuleDerived X) : Prop :=
  ∀ (sq : EtaleSquare f) [AlgebraicGeometry.Flat sq.map.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left],
    onEtaleSquare sq E

/-- Clause (2) unfolds to the scheme-level `V`-perfectness test on every étale scheme
square. -/
theorem everyEtaleSquare_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] (E : ModuleDerived X) :
    everyEtaleSquare f E ↔
      ∀ (sq : EtaleSquare f) [AlgebraicGeometry.Flat sq.map.left]
        [AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left],
        onEtaleSquare sq E :=
  sorry

/-- On any étale scheme square over `f`, clause (2) yields `V`-perfectness of `E|_U`. -/
theorem everyEtaleSquare_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] {E : ModuleDerived X}
    (h : everyEtaleSquare f E) (sq : EtaleSquare f)
    [AlgebraicGeometry.Flat sq.map.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left] :
    onEtaleSquare sq E :=
  sorry

/-- Clause (3): `E|_U` is `V`-perfect on some étale scheme square over `f` with
`U ⟶ X` surjective. -/
def existsSurjectiveEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] (E : ModuleDerived X) :
    Prop :=
  ∃ (sq : EtaleSquare f) (hFlat : AlgebraicGeometry.Flat sq.map.left)
      (hLFP : AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left),
    Surjective sq.left.hom ∧ @onEtaleSquare _ _ _ _ sq hFlat hLFP E

/-- Clause (3) unfolds to existence of an étale scheme square with surjective source
chart on which the scheme-level `V`-perfectness test holds. -/
theorem existsSurjectiveEtaleSquare_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] (E : ModuleDerived X) :
    existsSurjectiveEtaleSquare f E ↔
      ∃ (sq : EtaleSquare f) (hFlat : AlgebraicGeometry.Flat sq.map.left)
          (hLFP : AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left),
        Surjective sq.left.hom ∧ @onEtaleSquare _ _ _ _ sq hFlat hLFP E :=
  sorry

/-- The `RΓ` test on an affine étale scheme square: derived global sections of `E|_U`
are `𝒪_Y(V)`-perfect. -/
def affineSectionsRelative {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (sq : EtaleSquare f) [IsAffine sq.left.left.left] [IsAffine sq.right.left.left]
    [AlgebraicGeometry.Flat sq.map.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left]
    (E : ModuleDerived X) : Prop :=
  @DerivedCategory.IsPerfectOver (Scheme.globalSectionsRing sq.right.left.left) _
    (Scheme.globalSectionsRing sq.left.left.left) _
    (Scheme.Hom.appTop sq.map.left).hom.toAlgebra
    ((RingedSpace.moduleDerivedGlobalSections
        sq.left.left.left.toRingedSpace).obj
      (Eq.mp (derivedCategory_modules_eq_ringedSpace sq.left.left.left)
        ((restrictToSchemeDerived sq.left.left).obj
          ((pullback sq.left.hom).obj E))))

/-- The affine `RΓ` test unfolds to algebra-level relative perfectness of `RΓ(U, E)`
over `𝒪_Y(V)`. -/
theorem affineSectionsRelative_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} (sq : EtaleSquare f) [IsAffine sq.left.left.left]
    [IsAffine sq.right.left.left] [AlgebraicGeometry.Flat sq.map.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left]
    (E : ModuleDerived X) :
    affineSectionsRelative sq E ↔
      @DerivedCategory.IsPerfectOver (Scheme.globalSectionsRing sq.right.left.left) _
        (Scheme.globalSectionsRing sq.left.left.left) _
        (Scheme.Hom.appTop sq.map.left).hom.toAlgebra
        ((RingedSpace.moduleDerivedGlobalSections
            sq.left.left.left.toRingedSpace).obj
          (Eq.mp (derivedCategory_modules_eq_ringedSpace sq.left.left.left)
            ((restrictToSchemeDerived sq.left.left).obj
              ((pullback sq.left.hom).obj E)))) :=
  sorry

/-- Clause (4): on every affine étale scheme square over `f`, the complex `RΓ(U, E)`
is `𝒪_Y(V)`-perfect. -/
def everyAffineSections {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] (E : ModuleDerived X) : Prop :=
  ∀ (sq : EtaleSquare f) [IsAffine sq.left.left.left]
    [IsAffine sq.right.left.left] [AlgebraicGeometry.Flat sq.map.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left],
    affineSectionsRelative sq E

/-- Clause (4) unfolds to the affine `RΓ` test on every affine étale scheme square. -/
theorem everyAffineSections_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] (E : ModuleDerived X) :
    everyAffineSections f E ↔
      ∀ (sq : EtaleSquare f) [IsAffine sq.left.left.left]
        [IsAffine sq.right.left.left] [AlgebraicGeometry.Flat sq.map.left]
        [AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left],
        affineSectionsRelative sq E :=
  sorry

/-- On any affine étale scheme square over `f`, clause (4) yields the `RΓ`
`𝒪_Y(V)`-perfectness test. -/
theorem everyAffineSections_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] {E : ModuleDerived X}
    (h : everyAffineSections f E) (sq : EtaleSquare f)
    [IsAffine sq.left.left.left] [IsAffine sq.right.left.left]
    [AlgebraicGeometry.Flat sq.map.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation sq.map.left] :
    affineSectionsRelative sq E :=
  sorry

/-- Clauses (2) and (3) are equivalent for `E` in `D_QCoh(𝒪_X)`. -/
theorem everyEtaleSquare_iff_existsSurjectiveEtaleSquare {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    {E : ModuleDerived X} (hE : derivedQuasiCoherentModuleProperty X E) :
    everyEtaleSquare f E ↔ existsSurjectiveEtaleSquare f E :=
  sorry

/-- Clauses (2) and (4) are equivalent for `E` in `D_QCoh(𝒪_X)`. -/
theorem everyEtaleSquare_iff_everyAffineSections {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    {E : ModuleDerived X} (hE : derivedQuasiCoherentModuleProperty X E) :
    everyEtaleSquare f E ↔ everyAffineSections f E :=
  sorry

/-- `Y`-perfectness of `E` is equivalent to `V`-perfectness of `E|_U` on every étale
scheme square over `f`. -/
theorem iff_everyEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] {E : ModuleDerived X}
    (hE : derivedQuasiCoherentModuleProperty X E) :
    IsPerfectRelativeTo f E ↔ everyEtaleSquare f E :=
  sorry

/-- `Y`-perfectness of `E` is equivalent to `V`-perfectness of `E|_U` on some étale
scheme square over `f` with `U ⟶ X` surjective. -/
theorem iff_existsSurjectiveEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] {E : ModuleDerived X}
    (hE : derivedQuasiCoherentModuleProperty X E) :
    IsPerfectRelativeTo f E ↔ existsSurjectiveEtaleSquare f E :=
  sorry

/-- `Y`-perfectness of `E` is equivalent to `𝒪_Y(V)`-perfectness of `RΓ(U, E)` on every
affine étale scheme square over `f`. -/
theorem iff_everyAffineSections {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] {E : ModuleDerived X}
    (hE : derivedQuasiCoherentModuleProperty X E) :
    IsPerfectRelativeTo f E ↔ everyAffineSections f E :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo
