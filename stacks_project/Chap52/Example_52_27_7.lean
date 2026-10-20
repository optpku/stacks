module

public import ReasLib.AlgebraicGeometry.CompletedQuadricCone
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry

universe u

/- Example 52.27.7: the Picard group of the punctured spectrum of the completed quadric cone is nontrivial. -/
@[stacks 0F2J] #check
  (AlgebraicGeometry.CompletedQuadricCone.nontrivialPicardGroup :
    ∀ (k : Type u) [Field k],
      Nontrivial
        (Scheme.PicardGroup
          (AlgebraicGeometry.CompletedQuadricCone.puncturedOpen k).toScheme))

/- Example 52.27.7 (1): the ambient ring is the four-variable formal power-series ring. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.AmbientRing :
    ∀ (k : Type u) [Field k], Type u)

/- Example 52.27.7 (2): the four formal coordinates are available in the ambient ring. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.x :
    ∀ (k : Type u) [Field k],
      AlgebraicGeometry.CompletedQuadricCone.AmbientRing k)
#check
  (AlgebraicGeometry.CompletedQuadricCone.y :
    ∀ (k : Type u) [Field k],
      AlgebraicGeometry.CompletedQuadricCone.AmbientRing k)
#check
  (AlgebraicGeometry.CompletedQuadricCone.z :
    ∀ (k : Type u) [Field k],
      AlgebraicGeometry.CompletedQuadricCone.AmbientRing k)
#check
  (AlgebraicGeometry.CompletedQuadricCone.w :
    ∀ (k : Type u) [Field k],
      AlgebraicGeometry.CompletedQuadricCone.AmbientRing k)

/- Example 52.27.7 (3): the defining relation and quotient ring are explicit. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.relation :
    ∀ (k : Type u) [Field k],
      AlgebraicGeometry.CompletedQuadricCone.AmbientRing k)
#check
  (AlgebraicGeometry.CompletedQuadricCone.relationIdeal :
    ∀ (k : Type u) [Field k],
      Ideal (AlgebraicGeometry.CompletedQuadricCone.AmbientRing k))
#check
  (AlgebraicGeometry.CompletedQuadricCone.Ring :
    ∀ (k : Type u) [Field k], Type u)

/- Example 52.27.7 (4): the quotient coordinates and coordinate ideal are explicit. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.xBar :
    ∀ (k : Type u) [Field k], AlgebraicGeometry.CompletedQuadricCone.Ring k)
#check
  (AlgebraicGeometry.CompletedQuadricCone.yBar :
    ∀ (k : Type u) [Field k], AlgebraicGeometry.CompletedQuadricCone.Ring k)
#check
  (AlgebraicGeometry.CompletedQuadricCone.zBar :
    ∀ (k : Type u) [Field k], AlgebraicGeometry.CompletedQuadricCone.Ring k)
#check
  (AlgebraicGeometry.CompletedQuadricCone.wBar :
    ∀ (k : Type u) [Field k], AlgebraicGeometry.CompletedQuadricCone.Ring k)
#check
  (AlgebraicGeometry.CompletedQuadricCone.ideal :
    ∀ (k : Type u) [Field k],
      Ideal (AlgebraicGeometry.CompletedQuadricCone.Ring k))

/- Example 52.27.7 (5): the completed quadric cone is local and has a punctured spectrum. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.localRing :
    ∀ (k : Type u) [Field k],
      IsLocalRing (AlgebraicGeometry.CompletedQuadricCone.Ring k))
#check
  (AlgebraicGeometry.CompletedQuadricCone.puncturedOpen :
    ∀ (k : Type u) [Field k],
      (Spec
        (CommRingCat.of (AlgebraicGeometry.CompletedQuadricCone.Ring k))).Opens)
#check
  (AlgebraicGeometry.CompletedQuadricCone.divisor :
    ∀ (k : Type u) [Field k],
      (AlgebraicGeometry.CompletedQuadricCone.puncturedOpen k).toScheme.IdealSheafData)

/- Example 52.27.7 (6): the quotient coordinates satisfy the defining equation. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.relation_eq_zero :
    ∀ (k : Type u) [Field k],
      AlgebraicGeometry.CompletedQuadricCone.xBar k *
          AlgebraicGeometry.CompletedQuadricCone.yBar k =
        AlgebraicGeometry.CompletedQuadricCone.zBar k *
          AlgebraicGeometry.CompletedQuadricCone.wBar k)

/- Example 52.27.7 (7): the completed quadric cone has Krull dimension three. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.ringKrullDim_eq_three :
    ∀ (k : Type u) [Field k],
      ringKrullDim (AlgebraicGeometry.CompletedQuadricCone.Ring k) = (3 : WithBot ℕ∞))

/- Example 52.27.7 (8): the coordinate ideal defines an effective Cartier divisor. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.divisorIsEffectiveCartier :
    ∀ (k : Type u) [Field k],
      IsEffectiveCartierDivisor
        (AlgebraicGeometry.CompletedQuadricCone.divisor k).subschemeι)

/- Example 52.27.7 (9): the positive divisor sheaf has nonzero Picard class. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.picardClass_ne_zero :
    ∀ (k : Type u) [Field k],
      Scheme.Modules.picardClass
          (AlgebraicGeometry.CompletedQuadricCone.divisor k).associatedSheaf ≠
        (0 : Scheme.PicardGroup
          (AlgebraicGeometry.CompletedQuadricCone.puncturedOpen k).toScheme))

/- Example 52.27.7 (10): the quotient by the coordinate ideal has depth two. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.quotientDepth_eq_two :
    ∀ (k : Type u) [Field k],
      moduleDepth (AlgebraicGeometry.CompletedQuadricCone.Ring k)
        (AlgebraicGeometry.CompletedQuadricCone.Ring k ⧸
          AlgebraicGeometry.CompletedQuadricCone.ideal k) = 2)

/- Example 52.27.7 (11): the coordinate ideal has depth three. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.idealDepth_eq_three :
    ∀ (k : Type u) [Field k],
      Ideal.depth
          (IsLocalRing.maximalIdeal (AlgebraicGeometry.CompletedQuadricCone.Ring k))
          (AlgebraicGeometry.CompletedQuadricCone.ideal k) = 3)

/- Example 52.27.7 (12): the coordinate ideal is the global sections of the negative divisor sheaf. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.ideal_globalSections_iso :
    ∀ (k : Type u) [Field k],
      ModuleCat.of (AlgebraicGeometry.CompletedQuadricCone.Ring k)
          (AlgebraicGeometry.CompletedQuadricCone.ideal k) ≅
        Scheme.Hom.globalSectionsMod
          (AlgebraicGeometry.CompletedQuadricCone.puncturedOpen k).ι
          (AlgebraicGeometry.CompletedQuadricCone.divisor k).negSheaf)
#check
  (AlgebraicGeometry.CompletedQuadricCone.idealGlobalSectionsHom :
    ∀ (k : Type u) [Field k],
      ModuleCat.of (AlgebraicGeometry.CompletedQuadricCone.Ring k)
          (AlgebraicGeometry.CompletedQuadricCone.ideal k) ⟶
        Scheme.Hom.globalSectionsMod
          (AlgebraicGeometry.CompletedQuadricCone.puncturedOpen k).ι
          (AlgebraicGeometry.CompletedQuadricCone.divisor k).negSheaf)
#check
  (AlgebraicGeometry.CompletedQuadricCone.idealGlobalSectionsInv :
    ∀ (k : Type u) [Field k],
      Scheme.Hom.globalSectionsMod
          (AlgebraicGeometry.CompletedQuadricCone.puncturedOpen k).ι
          (AlgebraicGeometry.CompletedQuadricCone.divisor k).negSheaf ⟶
        ModuleCat.of (AlgebraicGeometry.CompletedQuadricCone.Ring k)
          (AlgebraicGeometry.CompletedQuadricCone.ideal k))
#check
  (AlgebraicGeometry.CompletedQuadricCone.idealGlobalSectionsHom_inclusion :
    ∀ (k : Type u) [Field k] (a : AlgebraicGeometry.CompletedQuadricCone.ideal k),
      AlgebraicGeometry.CompletedQuadricCone.idealGlobalSectionsInclusion k
          (AlgebraicGeometry.CompletedQuadricCone.idealGlobalSectionsHom k a) =
        Scheme.Hom.globalSectionsMap
          (AlgebraicGeometry.CompletedQuadricCone.puncturedOpen k).ι a)
#check
  (AlgebraicGeometry.CompletedQuadricCone.idealGlobalSectionsInv_coe :
    ∀ (k : Type u) [Field k]
      (s : Scheme.Hom.globalSectionsMod
        (AlgebraicGeometry.CompletedQuadricCone.puncturedOpen k).ι
        (AlgebraicGeometry.CompletedQuadricCone.divisor k).negSheaf),
      (AlgebraicGeometry.CompletedQuadricCone.idealGlobalSectionsInv k s :
          AlgebraicGeometry.CompletedQuadricCone.Ring k) =
        AlgebraicGeometry.CompletedQuadricCone.extendFunction k
          (AlgebraicGeometry.CompletedQuadricCone.idealGlobalSectionsInclusion k s))

/- Example 52.27.7 (13): the coordinate ideal is not principal. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.ideal_not_isPrincipal :
    ∀ (k : Type u) [Field k],
      ¬ (AlgebraicGeometry.CompletedQuadricCone.ideal k).IsPrincipal)

/- Example 52.27.7 (14): the negative divisor sheaf is not trivial. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.negSheaf_not_trivial :
    ∀ (k : Type u) [Field k],
      ¬ Nonempty
        ((AlgebraicGeometry.CompletedQuadricCone.divisor k).negSheaf ≅
          𝟙_ ((AlgebraicGeometry.CompletedQuadricCone.puncturedOpen k).toScheme.Modules)))

/- Example 52.27.7 (15): the coordinate ideal extends to each coordinate localization. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.localizedIdeal :
    ∀ (k : Type u) [Field k] (coordinate : AlgebraicGeometry.CompletedQuadricCone.Ring k),
      Ideal (Localization.Away coordinate))

/- Example 52.27.7 (16): the coordinate ideal is invertible on the first localization chart. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.localizedIdealXInvertible :
    ∀ (k : Type u) [Field k],
      Module.Invertible
        (Localization.Away (AlgebraicGeometry.CompletedQuadricCone.xBar k))
        (AlgebraicGeometry.CompletedQuadricCone.localizedIdeal k
          (AlgebraicGeometry.CompletedQuadricCone.xBar k)))

/- Example 52.27.7 (17): the coordinate ideal is invertible on the second localization chart. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.localizedIdealYInvertible :
    ∀ (k : Type u) [Field k],
      Module.Invertible
        (Localization.Away (AlgebraicGeometry.CompletedQuadricCone.yBar k))
        (AlgebraicGeometry.CompletedQuadricCone.localizedIdeal k
          (AlgebraicGeometry.CompletedQuadricCone.yBar k)))

/- Example 52.27.7 (18): the coordinate ideal is invertible on the third localization chart. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.localizedIdealZInvertible :
    ∀ (k : Type u) [Field k],
      Module.Invertible
        (Localization.Away (AlgebraicGeometry.CompletedQuadricCone.zBar k))
        (AlgebraicGeometry.CompletedQuadricCone.localizedIdeal k
          (AlgebraicGeometry.CompletedQuadricCone.zBar k)))

/- Example 52.27.7 (19): the coordinate ideal is invertible on the fourth localization chart. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.localizedIdealWInvertible :
    ∀ (k : Type u) [Field k],
      Module.Invertible
        (Localization.Away (AlgebraicGeometry.CompletedQuadricCone.wBar k))
        (AlgebraicGeometry.CompletedQuadricCone.localizedIdeal k
          (AlgebraicGeometry.CompletedQuadricCone.wBar k)))

/- Example 52.27.7 (20): the canonical map to global sections is bijective. -/
@[stacks 0F2J]
#check
  (AlgebraicGeometry.CompletedQuadricCone.globalSectionsMap_bijective :
    ∀ (k : Type u) [Field k],
      Function.Bijective
        (Scheme.Hom.globalSectionsMap
          (AlgebraicGeometry.CompletedQuadricCone.puncturedOpen k).ι))
