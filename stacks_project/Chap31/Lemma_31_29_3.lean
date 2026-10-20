module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RankOneReflexive.Section
import StacksCheckRecall

/-!
# Lemma 31.29.3

The isomorphism locus and section-power colimit for a rank-one reflexive module.

@stack 0EBN
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

#check @AlgebraicGeometry.Scheme.Modules.rankOneReflexiveSectionIsoLocusSet
#check @AlgebraicGeometry.Scheme.Modules.rankOneReflexiveSectionPower
#check @AlgebraicGeometry.Scheme.Modules.rankOneReflexiveSectionPowerMap
#check @AlgebraicGeometry.Scheme.Modules.rankOneReflexiveSectionPowerDiagram

/- Lemma 31.29.3 (1): For an integral locally Noetherian normal scheme and a coherent rank-one
reflexive `𝒪_X`-module, the locus where a section induces an isomorphism on stalks is open. -/
@[stacks 0EBN "open locus"]
#check
  (AlgebraicGeometry.Scheme.Modules.isOpen_rankOneReflexiveSectionIsoLocusSet :
    ∀ {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
      [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules],
      X.isNormal →
        ∀ (ℱ : X.Modules) [ℱ.IsCoherent] [Scheme.Modules.IsRankOneReflexive X ℱ]
          (s : 𝟙_ X.Modules ⟶ ℱ),
          IsOpen (Scheme.Modules.rankOneReflexiveSectionIsoLocusSet s))

/- Lemma 31.29.3 (2): In the same setup, if `U` is the open locus where the section induces
stalkwise isomorphisms, then the pushforward of `𝒪_U` is isomorphic to the colimit of the
reflexive section-power diagram. -/
@[stacks 0EBN "pushforward colimit"]
#check
  (AlgebraicGeometry.Scheme.Modules.pushforward_tensorUnit_iso_colimit_rankOneReflexiveSectionPowerDiagram :
    ∀ {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
      [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules],
      X.isNormal →
        ∀ (ℱ : X.Modules) [ℱ.IsCoherent] [Scheme.Modules.IsRankOneReflexive X ℱ]
          (s : 𝟙_ X.Modules ⟶ ℱ) (U : X.Opens),
          (U : Set X) = Scheme.Modules.rankOneReflexiveSectionIsoLocusSet s →
            Nonempty
              (((Scheme.Modules.pushforward U.ι).obj
                  (SheafOfModules.unit (U : Scheme).ringCatSheaf : (U : Scheme).Modules)) ≅
                colimit (Scheme.Modules.rankOneReflexiveSectionPowerDiagram s)))
