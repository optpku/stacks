module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.KFlat
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Pullback.Complex
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flat complex pullback along arbitrary morphisms of ringed topoi

For site-presented topoi with commutative structure sheaves, arbitrary ringed-topos pullback
preserves complexes which are K-flat with flat terms.  The universal object property in this file
quantifies over `RingedSite.ToposHom`, so it is independent of whether a morphism is presented by
a functor between sites.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe uX vX uY vY w

namespace RingedSite.ToposHom.modulePullbackComplex

section Preservation

variable {C : Type uX} [Category.{vX} C] {D : Type uY} [Category.{vY} D]
variable {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JX.HasSheafCompose (forget RingCat.{w})]
  [JY.HasSheafCompose (forget RingCat.{w})]
variable [HasWeakSheafify JX AddCommGrpCat.{w}]
  [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JY AddCommGrpCat.{w}]
  [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}

variable (f : RingedSite.ToposHom (RingedSite.ofCommRingSheaf JX OX)
  (RingedSite.ofCommRingSheaf JY OY))
variable [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]

/-- Pullback along an arbitrary morphism of ringed topoi preserves termwise flatness of
unbounded cochain complexes. -/
theorem isTermwiseFlat
    (K : CochainComplex
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ℤ)
    (hK : HomologicalComplex.IsTermwiseFlat K) :
    HomologicalComplex.IsTermwiseFlat (f.modulePullbackComplex.obj K) := sorry

/-- Pullback along an arbitrary morphism of ringed topoi preserves K-flatness for a K-flat
complex with flat terms. -/
theorem isKFlat_of_isTermwiseFlat
    (K : CochainComplex
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ℤ)
    (hKFlat : K.IsKFlat) (hK : HomologicalComplex.IsTermwiseFlat K) :
    (f.modulePullbackComplex.obj K).IsKFlat := sorry

/-- Pullback along an arbitrary morphism of ringed topoi preserves K-flatness and termwise
flatness together. -/
theorem isKFlat_and_isTermwiseFlat
    (K : CochainComplex
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ℤ)
    (hKFlat : K.IsKFlat) (hK : HomologicalComplex.IsTermwiseFlat K) :
    (f.modulePullbackComplex.obj K).IsKFlat ∧
      HomologicalComplex.IsTermwiseFlat (f.modulePullbackComplex.obj K) := sorry

/-- Pullback along an arbitrary morphism of ringed topoi preserves the canonical object
property of K-flat cochain complexes with flat terms. -/
@[stacks 0FU1 "arbitrary ringed-topos pullback"]
theorem termwiseFlat
    (K : CochainComplex
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ℤ)
    (hK : HomologicalComplex.KFlat.termwiseFlat (up ℤ) K) :
    HomologicalComplex.KFlat.termwiseFlat (up ℤ)
      (f.modulePullbackComplex.obj K) := sorry

end Preservation

section Universal

variable {D : Type uY} [Category.{vY} D] {JY : GrothendieckTopology D}
variable [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [JY.HasSheafCompose (forget RingCat.{w})]
variable [HasWeakSheafify JY AddCommGrpCat.{w}]
  [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {OY : Sheaf JY CommRingCat.{w}}

/-- The object property of complexes which are K-flat with flat terms before pullback and after
pullback along every arbitrary morphism of site-presented ringed topoi with commutative structure
sheaves in the source universes. -/
@[stacks 0FU1 "universal K-flat termwise-flat property"]
def universallyTermwiseFlat :
    ObjectProperty (CochainComplex
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ℤ) :=
  fun K ↦
    HomologicalComplex.KFlat.termwiseFlat (up ℤ) K ∧
      ∀ {C : Type uX} [Category.{vX} C] {JX : GrothendieckTopology C}
        [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
        [JX.HasSheafCompose (forget RingCat.{w})]
        [HasWeakSheafify JX AddCommGrpCat.{w}]
        [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
        {OX : Sheaf JX CommRingCat.{w}}
        (f : RingedSite.ToposHom (RingedSite.ofCommRingSheaf JX OX)
          (RingedSite.ofCommRingSheaf JY OY))
        [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint],
        HomologicalComplex.KFlat.termwiseFlat (up ℤ)
          (f.modulePullbackComplex.obj K)

/-- A complex is universally K-flat with flat terms when it belongs to
`universallyTermwiseFlat`. -/
abbrev UniversallyTermwiseFlat
    (K : CochainComplex
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ℤ) : Prop :=
  universallyTermwiseFlat.{uX, vX} (JY := JY) (OY := OY) K

/-- A universally K-flat termwise-flat complex has the underlying property before pullback. -/
theorem UniversallyTermwiseFlat.termwiseFlat
    {K : CochainComplex
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ℤ}
    (hK : UniversallyTermwiseFlat.{uX, vX} K) :
    HomologicalComplex.KFlat.termwiseFlat (up ℤ) K := sorry

/-- The universal property supplies K-flatness with flat terms after any arbitrary
ringed-topos pullback between commutative presentations. -/
theorem UniversallyTermwiseFlat.pullback
    {K : CochainComplex
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ℤ}
    (hK : UniversallyTermwiseFlat.{uX, vX} K)
    {C : Type uX} [Category.{vX} C] {JX : GrothendieckTopology C}
    [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [JX.HasSheafCompose (forget RingCat.{w})]
    [HasWeakSheafify JX AddCommGrpCat.{w}]
    [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {OX : Sheaf JX CommRingCat.{w}}
    (f : RingedSite.ToposHom (RingedSite.ofCommRingSheaf JX OX)
      (RingedSite.ofCommRingSheaf JY OY))
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] :
    HomologicalComplex.KFlat.termwiseFlat (up ℤ)
      (f.modulePullbackComplex.obj K) := sorry

/-- The K-flat termwise-flat property promotes to its universal form because arbitrary
ringed-topos pullback preserves it. -/
theorem UniversallyTermwiseFlat.of_termwiseFlat
    (K : CochainComplex
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ℤ)
    (hK : HomologicalComplex.KFlat.termwiseFlat (up ℤ) K) :
    UniversallyTermwiseFlat.{uX, vX} K := sorry

/-- Universal K-flat termwise-flatness is equivalent to the underlying property, since the
latter is preserved by every arbitrary ringed-topos pullback. -/
theorem universallyTermwiseFlat_iff
    (K : CochainComplex
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ℤ) :
    UniversallyTermwiseFlat.{uX, vX} K ↔
      HomologicalComplex.KFlat.termwiseFlat (up ℤ) K := sorry

end Universal

end RingedSite.ToposHom.modulePullbackComplex
