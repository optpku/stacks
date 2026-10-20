module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Principal.CohomologyDiagram
public import ReasLib.CategoryTheory.End.Power
public import ReasLib.AlgebraicGeometry.Scheme.Module.GlobalSections.Linear
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.FlatPullbackSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SequentialInverseSystem
open CategoryTheory.End.Power CategoryTheory.Linear.PrincipalPower
open CategoryTheory.DerivedCategory.PrincipalPower.CohomologyDiagram

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PrincipalCompletion

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- The inverse system whose stage `n` is `H^p(X, F / f ^ (n + 1) F)`, with scalars
restricted along the structure morphism `g : X ⟶ Spec A`. -/
abbrev quotientCohomologySystem
    (g : X ⟶ Spec (CommRingCat.of A)) (f : A) (F : X.Modules) (p : ℤ) :
    SequentialInverseSystem (ModuleCat.{u} A) :=
  quotientSystem
      (Scheme.Hom.globalSectionsMap g f) ((Scheme.Modules.toRingedSpace X).obj F) ⋙
    DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ) ⋙
    FlatPullbackSections.baseSections g ⋙ homology p

/-- Stage `n` of `quotientCohomologySystem g f F p` is the degree-`p` cohomology of
derived global sections of `F / f ^ (n + 1) F`. -/
theorem quotientCohomologySystem_obj
    (g : X ⟶ Spec (CommRingCat.of A)) (f : A) (F : X.Modules) (p : ℤ) (n : ℕ) :
    (quotientCohomologySystem g f F p).obj (op n) =
      (homology p).obj
        ((FlatPullbackSections.baseSections g).obj
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
            (quotientStage
              (Scheme.Hom.globalSectionsMap g f)
              ((Scheme.Modules.toRingedSpace X).obj F) n))) := sorry

/-- The successor map of `quotientCohomologySystem g f F p` is induced by the canonical
principal-power quotient map. -/
theorem quotientCohomologySystem_stepMap
    (g : X ⟶ Spec (CommRingCat.of A)) (f : A) (F : X.Modules) (p : ℤ) (n : ℕ) :
    (quotientCohomologySystem g f F p).stepMap n =
      (homology p).map
        ((FlatPullbackSections.baseSections g).map
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).map
            (quotientStep
              (Scheme.Hom.globalSectionsMap g f)
              ((Scheme.Modules.toRingedSpace X).obj F) n))) := sorry

/-- The cohomology diagram comparing ordinary completion, derived completion, and cohomology of
the inverse limit of the quotient sheaves, with upward columns from the first-derived-limit
terms. -/
structure CohomologyDiagram
    (g : X ⟶ Spec (CommRingCat.of A)) (f : A) (F : X.Modules) (p : ℤ) where
  /-- The first map in the ordinary-completion row. -/
  topLeftMap :
    topLeft f
        ((FlatPullbackSections.baseSections g).obj
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
            ((Scheme.Modules.toRingedSpace X).obj F))) p ⟶
      limit (quotientCohomologySystem g f F p)
  /-- The second map in the ordinary-completion row. -/
  topRightMap :
    limit (quotientCohomologySystem g f F p) ⟶
      right f
        ((FlatPullbackSections.baseSections g).obj
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
            ((Scheme.Modules.toRingedSpace X).obj F))) p
  /-- The top-row composite vanishes. -/
  topRowZero : topLeftMap ≫ topRightMap = 0
  /-- The first map in the derived-completion row. -/
  middleLeftMap :
    middleLeft f
        ((FlatPullbackSections.baseSections g).obj
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
            ((Scheme.Modules.toRingedSpace X).obj F))) p ⟶
      (homology p).obj
        ((FlatPullbackSections.baseSections g).obj
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
            (limit (quotientSystem
              (Scheme.Hom.globalSectionsMap g f)
              ((Scheme.Modules.toRingedSpace X).obj F)))))
  /-- The second map in the derived-completion row. -/
  middleRightMap :
      (homology p).obj
        ((FlatPullbackSections.baseSections g).obj
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
            (limit (quotientSystem
              (Scheme.Hom.globalSectionsMap g f)
              ((Scheme.Modules.toRingedSpace X).obj F))))) ⟶
      right f
        ((FlatPullbackSections.baseSections g).obj
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
            ((Scheme.Modules.toRingedSpace X).obj F))) p
  /-- The middle-row composite vanishes. -/
  middleRowZero : middleLeftMap ≫ middleRightMap = 0
  /-- The upward map from the left error term to derived completion of cohomology. -/
  leftBottomMap :
    bottomLeft f
        ((FlatPullbackSections.baseSections g).obj
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
            ((Scheme.Modules.toRingedSpace X).obj F))) p ⟶
      middleLeft f
        ((FlatPullbackSections.baseSections g).obj
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
            ((Scheme.Modules.toRingedSpace X).obj F))) p
  /-- The upward map from derived completion of cohomology to ordinary completion. -/
  leftTopMap :
    middleLeft f
        ((FlatPullbackSections.baseSections g).obj
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
            ((Scheme.Modules.toRingedSpace X).obj F))) p ⟶
      topLeft f
        ((FlatPullbackSections.baseSections g).obj
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
            ((Scheme.Modules.toRingedSpace X).obj F))) p
  /-- The left-column composite vanishes. -/
  leftColumnZero : leftBottomMap ≫ leftTopMap = 0
  /-- The upward map from the quotient-tower error term to cohomology of the sheaf limit. -/
  middleBottomMap :
    firstDerivedLimit (quotientCohomologySystem g f F (p - 1)) ⟶
      (homology p).obj
        ((FlatPullbackSections.baseSections g).obj
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
            (limit (quotientSystem
              (Scheme.Hom.globalSectionsMap g f)
              ((Scheme.Modules.toRingedSpace X).obj F)))))
  /-- The upward map from cohomology of the sheaf limit to the limit of quotient cohomology. -/
  middleTopMap :
    (homology p).obj
        ((FlatPullbackSections.baseSections g).obj
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
            (limit (quotientSystem
              (Scheme.Hom.globalSectionsMap g f)
              ((Scheme.Modules.toRingedSpace X).obj F))))) ⟶
      limit (quotientCohomologySystem g f F p)
  /-- The middle-column composite vanishes. -/
  middleColumnZero : middleBottomMap ≫ middleTopMap = 0
  /-- An isomorphism between the two first-derived-limit error terms. -/
  bottomIso :
    bottomLeft f
        ((FlatPullbackSections.baseSections g).obj
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
            ((Scheme.Modules.toRingedSpace X).obj F))) p ≅
      firstDerivedLimit (quotientCohomologySystem g f F (p - 1))
  /-- The top row is short exact. -/
  topRowShortExact :
    (ShortComplex.mk topLeftMap topRightMap topRowZero).ShortExact
  /-- The middle row is short exact. -/
  middleRowShortExact :
    (ShortComplex.mk middleLeftMap middleRightMap middleRowZero).ShortExact
  /-- The upward left column is short exact. -/
  leftColumnShortExact :
    (ShortComplex.mk leftBottomMap leftTopMap leftColumnZero).ShortExact
  /-- The upward middle column is short exact. -/
  middleColumnShortExact :
    (ShortComplex.mk middleBottomMap middleTopMap middleColumnZero).ShortExact
  /-- The square between the two middle rows and the top rows commutes on the left. -/
  leftTopSquare : CommSq middleLeftMap leftTopMap middleTopMap topLeftMap
  /-- The square between the two middle rows and the top rows commutes on the right. -/
  rightTopSquare :
    CommSq middleRightMap middleTopMap
      (𝟙 (right f
        ((FlatPullbackSections.baseSections g).obj
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
            ((Scheme.Modules.toRingedSpace X).obj F))) p)) topRightMap
  /-- The bottom square commutes through the chosen isomorphism. -/
  bottomSquare : CommSq bottomIso.hom leftBottomMap middleBottomMap middleLeftMap

namespace CohomologyDiagram

/-- Build the cohomology diagram from its row maps, upward column maps, bottom isomorphism,
exactness witnesses, and commutative squares. -/
def ofMaps
    {g : X ⟶ Spec (CommRingCat.of A)} {f : A} {F : X.Modules} {p : ℤ}
    (topLeftMap :
      topLeft f
          ((FlatPullbackSections.baseSections g).obj
            ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
              ((Scheme.Modules.toRingedSpace X).obj F))) p ⟶
        limit (quotientCohomologySystem g f F p))
    (topRightMap :
      limit (quotientCohomologySystem g f F p) ⟶
        right f
          ((FlatPullbackSections.baseSections g).obj
            ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
              ((Scheme.Modules.toRingedSpace X).obj F))) p)
    (topRowZero : topLeftMap ≫ topRightMap = 0)
    (middleLeftMap :
      middleLeft f
          ((FlatPullbackSections.baseSections g).obj
            ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
              ((Scheme.Modules.toRingedSpace X).obj F))) p ⟶
        (homology p).obj
          ((FlatPullbackSections.baseSections g).obj
            ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
              (limit (quotientSystem
                (Scheme.Hom.globalSectionsMap g f)
                ((Scheme.Modules.toRingedSpace X).obj F))))))
    (middleRightMap :
      (homology p).obj
          ((FlatPullbackSections.baseSections g).obj
            ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
              (limit (quotientSystem
                (Scheme.Hom.globalSectionsMap g f)
                ((Scheme.Modules.toRingedSpace X).obj F))))) ⟶
        right f
          ((FlatPullbackSections.baseSections g).obj
            ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
              ((Scheme.Modules.toRingedSpace X).obj F))) p)
    (middleRowZero : middleLeftMap ≫ middleRightMap = 0)
    (leftBottomMap :
      bottomLeft f
          ((FlatPullbackSections.baseSections g).obj
            ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
              ((Scheme.Modules.toRingedSpace X).obj F))) p ⟶
        middleLeft f
          ((FlatPullbackSections.baseSections g).obj
            ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
              ((Scheme.Modules.toRingedSpace X).obj F))) p)
    (leftTopMap :
      middleLeft f
          ((FlatPullbackSections.baseSections g).obj
            ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
              ((Scheme.Modules.toRingedSpace X).obj F))) p ⟶
        topLeft f
          ((FlatPullbackSections.baseSections g).obj
            ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
              ((Scheme.Modules.toRingedSpace X).obj F))) p)
    (leftColumnZero : leftBottomMap ≫ leftTopMap = 0)
    (middleBottomMap :
      firstDerivedLimit (quotientCohomologySystem g f F (p - 1)) ⟶
        (homology p).obj
        ((FlatPullbackSections.baseSections g).obj
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
            (limit (quotientSystem
              (Scheme.Hom.globalSectionsMap g f)
              ((Scheme.Modules.toRingedSpace X).obj F))))))
    (middleTopMap :
      (homology p).obj
          ((FlatPullbackSections.baseSections g).obj
            ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
              (limit (quotientSystem
                (Scheme.Hom.globalSectionsMap g f)
                ((Scheme.Modules.toRingedSpace X).obj F))))) ⟶
        limit (quotientCohomologySystem g f F p))
    (middleColumnZero : middleBottomMap ≫ middleTopMap = 0)
    (bottomIso :
      bottomLeft f
          ((FlatPullbackSections.baseSections g).obj
            ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
              ((Scheme.Modules.toRingedSpace X).obj F))) p ≅
        firstDerivedLimit (quotientCohomologySystem g f F (p - 1)))
    (topRowShortExact :
      (ShortComplex.mk topLeftMap topRightMap topRowZero).ShortExact)
    (middleRowShortExact :
      (ShortComplex.mk middleLeftMap middleRightMap middleRowZero).ShortExact)
    (leftColumnShortExact :
      (ShortComplex.mk leftBottomMap leftTopMap leftColumnZero).ShortExact)
    (middleColumnShortExact :
      (ShortComplex.mk middleBottomMap middleTopMap middleColumnZero).ShortExact)
    (leftTopSquare : CommSq middleLeftMap leftTopMap middleTopMap topLeftMap)
    (rightTopSquare :
      CommSq middleRightMap middleTopMap
        (𝟙 (right f
          ((FlatPullbackSections.baseSections g).obj
            ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
              ((Scheme.Modules.toRingedSpace X).obj F))) p)) topRightMap)
    (bottomSquare : CommSq bottomIso.hom leftBottomMap middleBottomMap middleLeftMap) :
    CohomologyDiagram g f F p where
  topLeftMap := topLeftMap
  topRightMap := topRightMap
  topRowZero := topRowZero
  middleLeftMap := middleLeftMap
  middleRightMap := middleRightMap
  middleRowZero := middleRowZero
  leftBottomMap := leftBottomMap
  leftTopMap := leftTopMap
  leftColumnZero := leftColumnZero
  middleBottomMap := middleBottomMap
  middleTopMap := middleTopMap
  middleColumnZero := middleColumnZero
  bottomIso := bottomIso
  topRowShortExact := topRowShortExact
  middleRowShortExact := middleRowShortExact
  leftColumnShortExact := leftColumnShortExact
  middleColumnShortExact := middleColumnShortExact
  leftTopSquare := leftTopSquare
  rightTopSquare := rightTopSquare
  bottomSquare := bottomSquare

/-- Both rows in the cohomology diagram are short exact. -/
theorem rowsShortExact {g : X ⟶ Spec (CommRingCat.of A)} {f : A} {F : X.Modules} {p : ℤ}
    (D : CohomologyDiagram g f F p) :
    (ShortComplex.mk D.topLeftMap D.topRightMap D.topRowZero).ShortExact ∧
      (ShortComplex.mk D.middleLeftMap D.middleRightMap D.middleRowZero).ShortExact := sorry

/-- Both upward columns in the cohomology diagram are short exact. -/
theorem columnsShortExact {g : X ⟶ Spec (CommRingCat.of A)} {f : A} {F : X.Modules} {p : ℤ}
    (D : CohomologyDiagram g f F p) :
    (ShortComplex.mk D.leftBottomMap D.leftTopMap D.leftColumnZero).ShortExact ∧
      (ShortComplex.mk D.middleBottomMap D.middleTopMap D.middleColumnZero).ShortExact := sorry

/-- The two upper squares commute, using the identity on the common Tate term. -/
theorem topSquares {g : X ⟶ Spec (CommRingCat.of A)} {f : A} {F : X.Modules} {p : ℤ}
    (D : CohomologyDiagram g f F p) :
    CommSq D.middleLeftMap D.leftTopMap D.middleTopMap D.topLeftMap ∧
      CommSq D.middleRightMap D.middleTopMap
        (𝟙 (right f
          ((FlatPullbackSections.baseSections g).obj
            ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
              ((Scheme.Modules.toRingedSpace X).obj F))) p)) D.topRightMap := sorry

end CohomologyDiagram

/-- If the kernels of the positive powers of multiplication by `f` on `F` stabilize, derived
global sections of the inverse limit of `F / f ^ n F` are isomorphic to the principal derived
completion of `RΓ(X, F)` over `A`. -/
theorem derivedSectionsLimit_isomorphic_derivedCompletion
    (g : X ⟶ Spec (CommRingCat.of A)) (f : A) (F : X.Modules) [F.IsQuasicoherent]
    (hstable : kernelStabilizes
      (RingedSpace.globalSectionMul (Scheme.Hom.globalSectionsMap g f)
        ((Scheme.Modules.toRingedSpace X).obj F))) :
    IsIsomorphic
      ((FlatPullbackSections.baseSections g).obj
        ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
          (limit (quotientSystem
            (Scheme.Hom.globalSectionsMap g f)
            ((Scheme.Modules.toRingedSpace X).obj F)))))
      (DerivedCategory.derivedCompletionOf (principalIdeal f) (principalIdeal_fg f)
        ((FlatPullbackSections.baseSections g).obj
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
            ((Scheme.Modules.toRingedSpace X).obj F)))) := sorry

/-- In every degree `p`, the completion row, the cohomology row, and the two upward Milnor
columns form a commutative diagram with exact rows and columns. -/
theorem existsCohomologyDiagram
    (g : X ⟶ Spec (CommRingCat.of A)) (f : A) (F : X.Modules) [F.IsQuasicoherent]
    (hstable : kernelStabilizes
      (RingedSpace.globalSectionMul (Scheme.Hom.globalSectionsMap g f)
        ((Scheme.Modules.toRingedSpace X).obj F))) (p : ℤ) :
    Nonempty (CohomologyDiagram g f F p) := sorry

end AlgebraicGeometry.Scheme.PrincipalCompletion
