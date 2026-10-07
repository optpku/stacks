module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve.Complementary

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex
open AlgebraicGeometry.Scheme.Modules.ClosedImmersion
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Editorial clarification of Stacks tag 0E34, checked against the uploaded
   proof in source/stacks-official-a04446e57ec1/tex/curves.tex:
   I' lives on Z and J' lives on Y, so their pushforwards use j and i,
   respectively. The formula for the dualizing module of Z likewise uses j
   for both pullback and pushforward. The uploaded statement prints i in that
   formula. We use the type-correct reading dictated by the displayed exact
   rows and the symmetry argument, not a literal ill-typed formula. -/

/- Lemma 53.4.6 (1) -/
@[stacks 0E34]
#check (AlgebraicGeometry.Scheme.cohenMacaulay_closedSubscheme :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      Scheme.CohenMacaulay Y)

/- Lemma 53.4.6 (2) -/
@[stacks 0E34]
#check (AlgebraicGeometry.Scheme.cohenMacaulay_complementaryClosure :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      Scheme.CohenMacaulay (complementaryClosure i))

/- Lemma 53.4.6 (3) -/
@[stacks 0E34]
#check (AlgebraicGeometry.Scheme.idealSheaf_closedSubscheme_pushforward :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      ∃ e : i.ker.toModule ≅
        (Modules.pushforward (complementaryClosureι i)).obj
          (idealOnComplementaryClosure i).toModule,
        e.hom ≫ (Modules.pushforward (complementaryClosureι i)).map
            (idealOnComplementaryClosure i).toSubobject.arrow =
          i.ker.toSubobject.arrow ≫
            SheafOfModules.unitToPushforwardObjUnit
              (complementaryClosureι i).toRingCatSheafHom)

/- Lemma 53.4.6 (4) -/
@[stacks 0E34]
#check (AlgebraicGeometry.Scheme.idealSheaf_complementaryClosure_pushforward :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      ∃ e : (complementaryClosureι i).ker.toModule ≅
        (Modules.pushforward i).obj (idealOnClosedSubscheme i).toModule,
        e.hom ≫ (Modules.pushforward i).map
            (idealOnClosedSubscheme i).toSubobject.arrow =
          (complementaryClosureι i).ker.toSubobject.arrow ≫
            SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)

/- Lemma 53.4.6 (5) -/
@[stacks 0E34]
#check (AlgebraicGeometry.Scheme.dualizingModule_closedSubscheme_isomorphic :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      IsIsomorphic (curveDualizingModule (i ≫ X.hom))
        ((idealOnClosedSubscheme i).toModule ⊗
          (Modules.pullback i).obj (curveDualizingModule X.hom)))

/- Lemma 53.4.6 (6) -/
@[stacks 0E34]
#check (AlgebraicGeometry.Scheme.pushforward_dualizingModule_closedSubscheme_isomorphic :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      IsIsomorphic
        ((Modules.pushforward i).obj (curveDualizingModule (i ≫ X.hom)))
        ((complementaryClosureι i).ker.toModule ⊗ curveDualizingModule X.hom))

/- Lemma 53.4.6 (7) -/
@[stacks 0E34]
#check (AlgebraicGeometry.Scheme.dualizingModule_complementaryClosure_isomorphic :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      IsIsomorphic (curveDualizingModule (complementaryClosureι i ≫ X.hom))
        ((idealOnComplementaryClosure i).toModule ⊗
          (Modules.pullback (complementaryClosureι i)).obj
            (curveDualizingModule X.hom)))

/- Lemma 53.4.6 (8) -/
@[stacks 0E34]
#check (AlgebraicGeometry.Scheme.pushforward_dualizingModule_complementaryClosure_isomorphic :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      IsIsomorphic
        ((Modules.pushforward (complementaryClosureι i)).obj
          (curveDualizingModule (complementaryClosureι i ≫ X.hom)))
        (i.ker.toModule ⊗ curveDualizingModule X.hom))

/- Lemma 53.4.6 (9) -/
@[stacks 0E34]
#check (AlgebraicGeometry.Scheme.dualizingMayerVietoris_shortExact :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      ((schemeTheoreticUnionShortComplex i.ker (complementaryClosureι i).ker).map
        (tensorRight (curveDualizingModule X.hom))).ShortExact)

/- Lemma 53.4.6 (10) -/
@[stacks 0E34]
#check (AlgebraicGeometry.Scheme.complementaryClosure_idealTensor_shortExact :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      (sequence (complementaryClosureι i) (curveDualizingModule X.hom)).ShortExact)

/- Lemma 53.4.6 (11) -/
@[stacks 0E34]
#check (AlgebraicGeometry.Scheme.closedSubscheme_idealTensor_shortExact :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      (sequence i (curveDualizingModule X.hom)).ShortExact)

/- Lemma 53.4.6 (12) -/
@[stacks 0E34]
#check (AlgebraicGeometry.Scheme.dualizingDirectSum_shortExact :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      (Modules.ClosedImmersion.complementaryIdealSumSequence i
        (curveDualizingModule X.hom)).ShortExact)

/- Lemma 53.4.6 (13) -/
@[stacks 0E34]
#check (AlgebraicGeometry.Scheme.closedSubscheme_restrictedDualizing_shortExact :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      (sequence (idealOnClosedSubscheme i).subschemeι
        ((Modules.pullback i).obj (curveDualizingModule X.hom))).ShortExact)

/- Lemma 53.4.6 (14) -/
@[stacks 0E34]
#check (AlgebraicGeometry.Scheme.complementaryClosure_restrictedDualizing_shortExact :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      (sequence (idealOnComplementaryClosure i).subschemeι
        ((Modules.pullback (complementaryClosureι i)).obj
          (curveDualizingModule X.hom))).ShortExact)

/- The ideal-sum object identifications. -/
#check (AlgebraicGeometry.Scheme.dualizingDirectSum_objects :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      let S := Modules.ClosedImmersion.complementaryIdealSumSequence i
        (curveDualizingModule X.hom)
      IsIsomorphic S.X₁
          ((Modules.pushforward i).obj (curveDualizingModule (i ≫ X.hom)) ⊞
            (Modules.pushforward (complementaryClosureι i)).obj
              (curveDualizingModule (complementaryClosureι i ≫ X.hom))) ∧
        IsIsomorphic S.X₃ (complementaryIntersectionStructureSheaf i))

#check (AlgebraicGeometry.Scheme.closedSubscheme_restrictedDualizing_objects :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      let S := sequence (idealOnClosedSubscheme i).subschemeι
        ((Modules.pullback i).obj (curveDualizingModule X.hom))
      IsIsomorphic S.X₁ (curveDualizingModule (i ≫ X.hom)) ∧
        IsIsomorphic S.X₃ (closedSubschemeStructureSheafOn
          (idealOnClosedSubscheme i)))

#check (AlgebraicGeometry.Scheme.complementaryClosure_restrictedDualizing_objects :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      let S := sequence (idealOnComplementaryClosure i).subschemeι
        ((Modules.pullback (complementaryClosureι i)).obj
          (curveDualizingModule X.hom))
      IsIsomorphic S.X₁ (curveDualizingModule (complementaryClosureι i ≫ X.hom)) ∧
        IsIsomorphic S.X₃ (closedSubschemeStructureSheafOn
          (idealOnComplementaryClosure i)))

#check (AlgebraicGeometry.Scheme.dualizingMayerVietoris_left_isomorphic :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      let S := (schemeTheoreticUnionShortComplex i.ker (complementaryClosureι i).ker).map
        (tensorRight (curveDualizingModule X.hom))
      IsIsomorphic S.X₁ (curveDualizingModule X.hom))

#check (AlgebraicGeometry.Scheme.dualizingMayerVietoris_middle_isomorphic :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      let S := (schemeTheoreticUnionShortComplex i.ker (complementaryClosureι i).ker).map
        (tensorRight (curveDualizingModule X.hom))
      IsIsomorphic S.X₂
        ((Modules.pushforward i).obj ((Modules.pullback i).obj
          (curveDualizingModule X.hom)) ⊞
          (Modules.pushforward (complementaryClosureι i)).obj
            ((Modules.pullback (complementaryClosureι i)).obj
              (curveDualizingModule X.hom))))

#check (AlgebraicGeometry.Scheme.dualizingMayerVietoris_right_isomorphic :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      let S := (schemeTheoreticUnionShortComplex i.ker (complementaryClosureι i).ker).map
        (tensorRight (curveDualizingModule X.hom))
      IsIsomorphic S.X₃ (complementaryIntersectionStructureSheaf i))

#check (AlgebraicGeometry.Scheme.complementaryClosure_idealTensor_left_isomorphic :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      IsIsomorphic (sequence (complementaryClosureι i)
        (curveDualizingModule X.hom)).X₁
          ((Modules.pushforward i).obj (curveDualizingModule (i ≫ X.hom))))

#check (AlgebraicGeometry.Scheme.closedSubscheme_idealTensor_left_isomorphic :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      [Gorenstein X.left] → [IsReduced X.left] →
      [TopologicalSpace.EquidimensionalSpace X.left] →
      topologicalKrullDim X.left = 1 → {Y : Scheme.{u}} → (i : Y ⟶ X.left) →
      [IsClosedImmersion i] → [IsReduced Y] →
      [TopologicalSpace.EquidimensionalSpace Y] → topologicalKrullDim Y = 1 →
      IsIsomorphic (sequence i (curveDualizingModule X.hom)).X₁
        ((Modules.pushforward (complementaryClosureι i)).obj
          (curveDualizingModule (complementaryClosureι i ≫ X.hom))))

end AlgebraicGeometry.Scheme

end
