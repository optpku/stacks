/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Determinant.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.DeterminantComparison

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Tate

open PerfectDerived.TorNegOneZero

/-- Pullback data between the fixed determinant constructions of a determinant system. -/
structure DeterminantComparison.{v}
    (D : (X : Scheme.{v}) → Determinant X) {X Y : Scheme.{v}} (f : X ⟶ Y) where
  /-- The natural comparison between pullback of determinant lines and determinant after
  derived pullback. -/
  lineNatIso :
    Determinant.lineFunctor (D Y) ⋙ Scheme.Modules.pullback f ≅
      (PerfectDerived.TorNegOneZero.pullback f).core ⋙ Determinant.lineFunctor (D X)
  /-- Derived pullback preserves the rank-zero locus. -/
  rankZero : ∀ L : PerfectDerived.TorNegOneZero Y, (D Y).isRankZero L →
    (D X).isRankZero ((PerfectDerived.TorNegOneZero.pullback f).obj L)
  /-- The comparison carries the pulled-back canonical section to the canonical section. -/
  canonicalElement : ∀ (L : PerfectDerived.TorNegOneZero Y) (hL : (D Y).isRankZero L),
    SheafOfModules.sectionsMap (lineNatIso.hom.app ⟨L⟩)
        (RingedSpace.Hom.pullbackSections f.toShHom
          (RingedSpace.sectionFromTop ((D Y).line L) ((D Y).canonicalElement L hL))) =
      RingedSpace.sectionFromTop
        ((D X).line ((PerfectDerived.TorNegOneZero.pullback f).obj L))
        ((D X).canonicalElement ((PerfectDerived.TorNegOneZero.pullback f).obj L)
          (rankZero L hL))

namespace DeterminantComparison

/-- Construct a fixed-endpoint determinant comparison from its comparison data. -/
def of
    {D : (X : Scheme.{u}) → Determinant X} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (lineNatIso :
      Determinant.lineFunctor (D Y) ⋙ Scheme.Modules.pullback f ≅
        (PerfectDerived.TorNegOneZero.pullback f).core ⋙ Determinant.lineFunctor (D X))
    (rankZero : ∀ L : PerfectDerived.TorNegOneZero Y, (D Y).isRankZero L →
      (D X).isRankZero ((PerfectDerived.TorNegOneZero.pullback f).obj L))
    (canonicalElement :
      ∀ (L : PerfectDerived.TorNegOneZero Y) (hL : (D Y).isRankZero L),
        SheafOfModules.sectionsMap (lineNatIso.hom.app ⟨L⟩)
            (RingedSpace.Hom.pullbackSections f.toShHom
              (RingedSpace.sectionFromTop ((D Y).line L) ((D Y).canonicalElement L hL))) =
          RingedSpace.sectionFromTop
            ((D X).line ((PerfectDerived.TorNegOneZero.pullback f).obj L))
            ((D X).canonicalElement ((PerfectDerived.TorNegOneZero.pullback f).obj L)
              (rankZero L hL))) :
    DeterminantComparison D f :=
  ⟨lineNatIso, rankZero, canonicalElement⟩

/-- Regard a fixed-endpoint determinant comparison as ordinary determinant pullback data. -/
def toPullback
    {D : (X : Scheme.{u}) → Determinant X} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (P : DeterminantComparison D f) : Determinant.Pullback f where
  source := D Y
  target := D X
  lineNatIso := P.lineNatIso
  rankZero := P.rankZero
  canonicalElement := P.canonicalElement

/-- The determinant-line isomorphism supplied by a fixed-endpoint comparison. -/
def lineIso
    {D : (X : Scheme.{u}) → Determinant X} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (P : DeterminantComparison D f) (K : PerfectDerived.TorNegOneZero Y) :
    (Scheme.Modules.pullback f).obj ((D Y).line K) ≅
      (D X).line ((PerfectDerived.TorNegOneZero.pullback f).obj K) :=
  P.lineNatIso.app ⟨K⟩

/-- The fixed-endpoint determinant-line comparison is the corresponding component of the
stored natural isomorphism. -/
theorem lineIso_def
    {D : (X : Scheme.{u}) → Determinant X} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (P : DeterminantComparison D f) (K : PerfectDerived.TorNegOneZero Y) :
    P.lineIso K = P.lineNatIso.app ⟨K⟩ := sorry

/-- Conversion to ordinary pullback data preserves the determinant-line comparison. -/
theorem toPullback_lineIso
    {D : (X : Scheme.{u}) → Determinant X} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (P : DeterminantComparison D f) (K : PerfectDerived.TorNegOneZero Y) :
    P.toPullback.lineIso K = P.lineIso K := sorry

end DeterminantComparison

/-- A coherent choice of determinant construction on schemes, including fixed pullback
comparisons and their identity and composition laws. -/
structure DeterminantSystem.{v} where
  /-- The chosen determinant construction on each scheme. -/
  determinant : (X : Scheme.{v}) → Determinant X
  /-- The chosen determinant comparison along each scheme morphism. -/
  comparison : ∀ {X Y : Scheme.{v}} (f : X ⟶ Y), DeterminantComparison determinant f
  /-- The canonical identification of derived pullback along an identity. -/
  identityObjectIso : ∀ (X : Scheme.{v}) (K : PerfectDerived.TorNegOneZero X),
    (PerfectDerived.TorNegOneZero.pullback (𝟙 X)).obj K ≅ K
  /-- The canonical identification of derived pullback along a composite with iterated
  derived pullback. -/
  compositionObjectIso : ∀ {X Y Z : Scheme.{v}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : PerfectDerived.TorNegOneZero Z),
    (PerfectDerived.TorNegOneZero.pullback (f ≫ g)).obj K ≅
      (PerfectDerived.TorNegOneZero.pullback f).obj
        ((PerfectDerived.TorNegOneZero.pullback g).obj K)
  /-- The chosen determinant comparison along an identity is the canonical identity
  comparison. -/
  comparison_identity : ∀ (X : Scheme.{v}) (K : PerfectDerived.TorNegOneZero X),
    (comparison (𝟙 X)).lineIso K ≪≫
        Scheme.RelativeDifferentials.determinantLineIso (determinant X) (identityObjectIso X K) =
      (Scheme.Modules.pullbackId X).app ((determinant X).line K)
  /-- The chosen determinant comparison along a composite agrees with the composite of the
  two chosen comparisons. -/
  comparison_comp : ∀ {X Y Z : Scheme.{v}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : PerfectDerived.TorNegOneZero Z),
    (Scheme.Modules.pullbackComp f g).app ((determinant Z).line K) ≪≫
          (comparison (f ≫ g)).lineIso K ≪≫
          Scheme.RelativeDifferentials.determinantLineIso
            (determinant X) (compositionObjectIso f g K) =
      (Scheme.Modules.pullback f).mapIso ((comparison g).lineIso K) ≪≫
        (comparison f).lineIso ((PerfectDerived.TorNegOneZero.pullback g).obj K)

namespace DeterminantSystem

/-- Construct a coherent determinant system from its determinant data and comparison laws. -/
def of
    (determinant : (X : Scheme.{u}) → Determinant X)
    (comparison : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), DeterminantComparison determinant f)
    (identityObjectIso : ∀ (X : Scheme.{u}) (K : PerfectDerived.TorNegOneZero X),
      (PerfectDerived.TorNegOneZero.pullback (𝟙 X)).obj K ≅ K)
    (compositionObjectIso : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      (K : PerfectDerived.TorNegOneZero Z),
      (PerfectDerived.TorNegOneZero.pullback (f ≫ g)).obj K ≅
        (PerfectDerived.TorNegOneZero.pullback f).obj
          ((PerfectDerived.TorNegOneZero.pullback g).obj K))
    (comparison_identity : ∀ (X : Scheme.{u}) (K : PerfectDerived.TorNegOneZero X),
      (comparison (𝟙 X)).lineIso K ≪≫
          Scheme.RelativeDifferentials.determinantLineIso
            (determinant X) (identityObjectIso X K) =
        (Scheme.Modules.pullbackId X).app ((determinant X).line K))
    (comparison_comp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      (K : PerfectDerived.TorNegOneZero Z),
      (Scheme.Modules.pullbackComp f g).app ((determinant Z).line K) ≪≫
            (comparison (f ≫ g)).lineIso K ≪≫
            Scheme.RelativeDifferentials.determinantLineIso
              (determinant X) (compositionObjectIso f g K) =
        (Scheme.Modules.pullback f).mapIso ((comparison g).lineIso K) ≪≫
          (comparison f).lineIso ((PerfectDerived.TorNegOneZero.pullback g).obj K)) :
    DeterminantSystem.{u} :=
  ⟨determinant, comparison, identityObjectIso, compositionObjectIso,
    comparison_identity, comparison_comp⟩

/-- The ordinary determinant pullback data selected by a coherent determinant system. -/
def pullback (S : DeterminantSystem.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Determinant.Pullback f :=
  (S.comparison f).toPullback

/-- The source determinant of the selected pullback comparison is the system's determinant
on the target scheme. -/
theorem pullback_source (S : DeterminantSystem.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (S.pullback f).source = S.determinant Y := sorry

end DeterminantSystem

end AlgebraicGeometry.Scheme.Hom.Tate
