module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Square
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Relative.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pullback.Preservation
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsMPseudoCoherentOver

/-- On an étale scheme square, every scheme-derived comparison preimage of the
derived pullback of `E` is `m`-pseudo-coherent relative to the target chart. -/
def onEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} (sq : EtaleSquare f)
    [AlgebraicGeometry.LocallyOfFiniteType sq.map.left]
    (E : ModuleDerived X) (m : ℤ) : Prop :=
  ∀ E0 : Scheme.DerivedQCoh sq.left.left.left,
    isEpsilonStarPullback sq.left.left ((ModuleDerived.pullback sq.left.hom).obj E) E0 →
      Scheme.ModuleDerived.IsMPseudoCoherentOver sq.map.left E0.obj m

/-- The étale-square test is relative `m`-pseudo-coherence of every scheme-derived
comparison preimage of the derived pullback to the source chart. -/
theorem onEtaleSquare_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} (sq : EtaleSquare f)
    [AlgebraicGeometry.LocallyOfFiniteType sq.map.left]
    (E : ModuleDerived X) (m : ℤ) :
    onEtaleSquare sq E m ↔
      ∀ E0 : Scheme.DerivedQCoh sq.left.left.left,
        isEpsilonStarPullback sq.left.left ((ModuleDerived.pullback sq.left.hom).obj E) E0 →
          Scheme.ModuleDerived.IsMPseudoCoherentOver sq.map.left E0.obj m :=
  Iff.rfl

/-- The restriction of a derived module is relatively `m`-pseudo-coherent on every
étale scheme square over the morphism. -/
def everyEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [LocallyOfFiniteType f] (E : ModuleDerived X) (m : ℤ) : Prop :=
  ∀ (sq : EtaleSquare f) [AlgebraicGeometry.LocallyOfFiniteType sq.map.left],
    onEtaleSquare sq E m

/-- The universal étale-square condition is equivalent to the scheme-comparison
test on every étale scheme square. -/
theorem everyEtaleSquare_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [LocallyOfFiniteType f] (E : ModuleDerived X) (m : ℤ) :
    everyEtaleSquare f E m ↔
      ∀ (sq : EtaleSquare f)
        [AlgebraicGeometry.LocallyOfFiniteType sq.map.left],
        onEtaleSquare sq E m :=
  Iff.rfl

/-- The universal étale-square condition gives relative `m`-pseudo-coherence
on any étale scheme square. -/
theorem everyEtaleSquare_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [LocallyOfFiniteType f] {E : ModuleDerived X} {m : ℤ}
    (h : everyEtaleSquare f E m) (sq : EtaleSquare f)
    [AlgebraicGeometry.LocallyOfFiniteType sq.map.left] :
    onEtaleSquare sq E m :=
  h sq

/-- The restriction of a derived module is relatively `m`-pseudo-coherent on some
étale scheme square whose source chart is surjective. -/
def existsSurjectiveEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [LocallyOfFiniteType f] (E : ModuleDerived X) (m : ℤ) : Prop :=
  ∃ (sq : EtaleSquare f)
      (h_lft : AlgebraicGeometry.LocallyOfFiniteType sq.map.left),
    Surjective sq.left.hom ∧ @onEtaleSquare S X Y f sq h_lft E m

/-- The surjective étale-square condition is equivalent to the existence of a surjective
source chart on which every scheme-derived comparison preimage is relatively
`m`-pseudo-coherent. -/
theorem existsSurjectiveEtaleSquare_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [LocallyOfFiniteType f] (E : ModuleDerived X) (m : ℤ) :
    existsSurjectiveEtaleSquare f E m ↔
      ∃ (sq : EtaleSquare f)
          (h_lft : AlgebraicGeometry.LocallyOfFiniteType sq.map.left),
        Surjective sq.left.hom ∧ @onEtaleSquare S X Y f sq h_lft E m :=
  Iff.rfl

/-- On an affine étale scheme square, derived global sections of every
scheme-derived comparison preimage of `E|_U` are `m`-pseudo-coherent relative to
the global-sections ring of the target chart, using its induced finite type algebra. -/
def affineSectionsRelative {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} (sq : EtaleSquare f)
    [IsAffine sq.left.left.left] [IsAffine sq.right.left.left]
    [AlgebraicGeometry.LocallyOfFiniteType sq.map.left] (E : ModuleDerived X)
    (m : ℤ) : Prop :=
  ∀ E0 : Scheme.DerivedQCoh sq.left.left.left,
    isEpsilonStarPullback sq.left.left ((ModuleDerived.pullback sq.left.hom).obj E) E0 →
      ∃ hFT : (Scheme.Hom.appTop sq.map.left).hom.FiniteType,
        @DerivedCategory.IsMPseudoCoherentRelativeTo
          (Scheme.globalSectionsRing sq.right.left.left) _
          (Scheme.globalSectionsRing sq.left.left.left) _
          (Scheme.Hom.appTop sq.map.left).hom.toAlgebra hFT
          ((RingedSpace.moduleDerivedGlobalSections
            sq.left.left.left.toRingedSpace).obj E0.obj) m

/-- The affine comparison test is finite type of the induced global-sections algebra
and relative `m`-pseudo-coherence of the derived global sections of every
scheme-derived comparison preimage. -/
theorem affineSectionsRelative_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} (sq : EtaleSquare f)
    [IsAffine sq.left.left.left]
    [IsAffine sq.right.left.left]
    [AlgebraicGeometry.LocallyOfFiniteType sq.map.left] (E : ModuleDerived X)
    (m : ℤ) :
    affineSectionsRelative sq E m ↔
      ∀ E0 : Scheme.DerivedQCoh sq.left.left.left,
        isEpsilonStarPullback sq.left.left ((ModuleDerived.pullback sq.left.hom).obj E) E0 →
          ∃ hFT : (Scheme.Hom.appTop sq.map.left).hom.FiniteType,
            @DerivedCategory.IsMPseudoCoherentRelativeTo
              (Scheme.globalSectionsRing sq.right.left.left) _
              (Scheme.globalSectionsRing sq.left.left.left) _
              (Scheme.Hom.appTop sq.map.left).hom.toAlgebra hFT
              ((RingedSpace.moduleDerivedGlobalSections
                sq.left.left.left.toRingedSpace).obj E0.obj) m :=
  Iff.rfl

/-- On every affine étale scheme square, derived global sections of the restricted module
are `m`-pseudo-coherent relative to the global-sections ring of the target chart. -/
def everyAffineSections {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [LocallyOfFiniteType f] (E : ModuleDerived X) (m : ℤ) : Prop :=
  ∀ (sq : EtaleSquare f) [IsAffine sq.left.left.left]
    [IsAffine sq.right.left.left]
    [AlgebraicGeometry.LocallyOfFiniteType sq.map.left],
    affineSectionsRelative sq E m

/-- The universal affine condition is equivalent to the derived global-sections test
on every affine étale scheme square. -/
theorem everyAffineSections_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [LocallyOfFiniteType f] (E : ModuleDerived X) (m : ℤ) :
    everyAffineSections f E m ↔
      ∀ (sq : EtaleSquare f) [IsAffine sq.left.left.left]
        [IsAffine sq.right.left.left]
        [AlgebraicGeometry.LocallyOfFiniteType sq.map.left],
        affineSectionsRelative sq E m :=
  Iff.rfl

/-- The universal affine condition gives the relative `m`-pseudo-coherence test
for derived global sections on any affine étale scheme square. -/
theorem everyAffineSections_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [LocallyOfFiniteType f] {E : ModuleDerived X} {m : ℤ}
    (h : everyAffineSections f E m) (sq : EtaleSquare f)
    [IsAffine sq.left.left.left] [IsAffine sq.right.left.left]
    [AlgebraicGeometry.LocallyOfFiniteType sq.map.left] :
    affineSectionsRelative sq E m :=
  h sq

/-- For a derived module with quasi-coherent cohomology, relative `m`-pseudo-coherence on
every étale scheme square is equivalent to the same condition on one square with
surjective source chart. -/
theorem everyEtaleSquare_iff_existsSurjectiveEtaleSquare {S : Scheme.{u}}
    {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [LocallyOfFiniteType f]
    {E : ModuleDerived X} (hE : derivedQuasiCoherentModuleProperty X E) (m : ℤ) :
    everyEtaleSquare f E m ↔ existsSurjectiveEtaleSquare f E m :=
  sorry

/-- For a derived module with quasi-coherent cohomology, relative `m`-pseudo-coherence on
every étale scheme square is equivalent to the derived global-sections condition on
every affine étale scheme square. -/
theorem everyEtaleSquare_iff_everyAffineSections {S : Scheme.{u}}
    {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [LocallyOfFiniteType f]
    {E : ModuleDerived X} (hE : derivedQuasiCoherentModuleProperty X E) (m : ℤ) :
    everyEtaleSquare f E m ↔ everyAffineSections f E m :=
  sorry

/-- For a locally finite type morphism and a derived module with quasi-coherent
cohomology, relative `m`-pseudo-coherence on every étale scheme square, on one
square with surjective source chart, and the derived global-sections condition on
every affine étale scheme square are equivalent. -/
theorem tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [LocallyOfFiniteType f] {E : ModuleDerived X}
    (hE : derivedQuasiCoherentModuleProperty X E) (m : ℤ) :
    List.TFAE [IsMPseudoCoherentOver.everyEtaleSquare f E m,
      IsMPseudoCoherentOver.existsSurjectiveEtaleSquare f E m,
      IsMPseudoCoherentOver.everyAffineSections f E m] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsMPseudoCoherentOver
