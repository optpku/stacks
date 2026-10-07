module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Complementary
public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.ClosedImmersion.Complementary
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve.ClosedImmersion
public import ReasLib.Topology.KrullDimension.Equidimensional
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Union

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

variable {k : Type u} [Field k]
variable (X : SchemeOverField k)
variable [h_proper : IsProper X.hom]
variable [h_gorenstein : Gorenstein X.left]
variable [h_X_reduced : IsReduced X.left]
variable [h_X_equidimensional : TopologicalSpace.EquidimensionalSpace X.left]
variable (h_X_dimension : topologicalKrullDim X.left = 1)
variable {Y : Scheme.{u}} (i : Y ⟶ X.left)
variable [h_i_closed : IsClosedImmersion i]
variable [h_Y_reduced : IsReduced Y]
variable [h_Y_equidimensional : TopologicalSpace.EquidimensionalSpace Y]
variable (h_Y_dimension : topologicalKrullDim Y = 1)

include h_proper h_gorenstein h_X_reduced h_X_equidimensional h_X_dimension
  h_i_closed h_Y_reduced h_Y_equidimensional h_Y_dimension

/-- A reduced one-dimensional closed subscheme of a Gorenstein proper curve is Cohen--Macaulay. -/
theorem cohenMacaulay_closedSubscheme : Scheme.CohenMacaulay Y := sorry

/-- The complementary closure of a reduced one-dimensional closed subscheme of a Gorenstein
proper curve is Cohen--Macaulay. -/
theorem cohenMacaulay_complementaryClosure :
    Scheme.CohenMacaulay (complementaryClosure i) := sorry

/-- The ideal sheaf of the closed subscheme is the pushforward of its restriction to the
complementary closure, compatibly with the ideal inclusion. -/
theorem idealSheaf_closedSubscheme_pushforward :
    ∃ e : i.ker.toModule ≅
        (Modules.pushforward (complementaryClosureι i)).obj
          (idealOnComplementaryClosure i).toModule,
      e.hom ≫ (Modules.pushforward (complementaryClosureι i)).map
          (idealOnComplementaryClosure i).toSubobject.arrow =
        (i.ker).toSubobject.arrow ≫ SheafOfModules.unitToPushforwardObjUnit
          (complementaryClosureι i).toRingCatSheafHom := sorry

/-- The ideal sheaf of the complementary closure is the pushforward of its restriction to the
closed subscheme, compatibly with the ideal inclusion. -/
theorem idealSheaf_complementaryClosure_pushforward :
    ∃ e : (complementaryClosureι i).ker.toModule ≅
        (Modules.pushforward i).obj (idealOnClosedSubscheme i).toModule,
      e.hom ≫ (Modules.pushforward i).map
          (idealOnClosedSubscheme i).toSubobject.arrow =
        (complementaryClosureι i).ker.toSubobject.arrow ≫
          SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom := sorry

/-- The dualizing module of the closed subscheme is the intersection ideal tensored with the
pullback of the ambient dualizing module. -/
theorem dualizingModule_closedSubscheme_isomorphic :
    IsIsomorphic (curveDualizingModule (i ≫ X.hom))
      ((idealOnClosedSubscheme i).toModule ⊗
        (Scheme.Modules.pullback i).obj (curveDualizingModule X.hom)) := sorry

/-- The pushforward of the dualizing module of the closed subscheme is the complementary ideal
tensored with the ambient dualizing module. -/
theorem pushforward_dualizingModule_closedSubscheme_isomorphic :
    IsIsomorphic
      ((Scheme.Modules.pushforward i).obj (curveDualizingModule (i ≫ X.hom)))
      ((complementaryClosureι i).ker.toModule ⊗ curveDualizingModule X.hom) := sorry

/-- The dualizing module of the complementary closure is its intersection ideal tensored with the
pullback of the ambient dualizing module. -/
theorem dualizingModule_complementaryClosure_isomorphic :
    IsIsomorphic (curveDualizingModule (complementaryClosureι i ≫ X.hom))
      ((idealOnComplementaryClosure i).toModule ⊗
        (Scheme.Modules.pullback (complementaryClosureι i)).obj
          (curveDualizingModule X.hom)) := sorry

/-- The pushforward of the dualizing module of the complementary closure is the ideal of the
closed subscheme tensored with the ambient dualizing module. -/
theorem pushforward_dualizingModule_complementaryClosure_isomorphic :
    IsIsomorphic
      ((Scheme.Modules.pushforward (complementaryClosureι i)).obj
        (curveDualizingModule (complementaryClosureι i ≫ X.hom)))
      (i.ker.toModule ⊗ curveDualizingModule X.hom) := sorry

/-- The Mayer--Vietoris structure-sheaf sequence tensored with the ambient dualizing module is
short exact. -/
theorem dualizingMayerVietoris_shortExact :
    ((schemeTheoreticUnionShortComplex i.ker (complementaryClosureι i).ker).map
      (tensorRight (curveDualizingModule X.hom))).ShortExact := sorry

/-- The ideal-tensor sequence for the complementary closure and the ambient dualizing module is
short exact. -/
theorem complementaryClosure_idealTensor_shortExact :
    (sequence (complementaryClosureι i)
      (curveDualizingModule X.hom)).ShortExact := sorry

/-- The ideal-tensor sequence for the closed subscheme and the ambient dualizing module is short
exact. -/
theorem closedSubscheme_idealTensor_shortExact :
    (sequence i (curveDualizingModule X.hom)).ShortExact := sorry

/-- The direct sum of the two ideal-tensor inclusions into the dualizing module, followed by
restriction to the intersection, is short exact. -/
theorem dualizingDirectSum_shortExact :
    (Modules.ClosedImmersion.complementaryIdealSumSequence i
      (curveDualizingModule X.hom)).ShortExact := sorry

/-- The ideal-tensor and restriction sequence on the closed subscheme is short exact. -/
theorem closedSubscheme_restrictedDualizing_shortExact :
    (sequence (idealOnClosedSubscheme i).subschemeι
      ((Modules.pullback i).obj (curveDualizingModule X.hom))).ShortExact := sorry

/-- The ideal-tensor and restriction sequence on the complementary closure is short exact. -/
theorem complementaryClosure_restrictedDualizing_shortExact :
    (sequence (idealOnComplementaryClosure i).subschemeι
      ((Modules.pullback (complementaryClosureι i)).obj
        (curveDualizingModule X.hom))).ShortExact := sorry

/-- The ideal-sum sequence identifies its first object with the two pushed-forward dualizing
modules and its third object with the intersection structure sheaf. -/
theorem dualizingDirectSum_objects :
    let S := Modules.ClosedImmersion.complementaryIdealSumSequence i
      (curveDualizingModule X.hom)
    IsIsomorphic S.X₁
        ((Modules.pushforward i).obj (curveDualizingModule (i ≫ X.hom)) ⊞
          (Modules.pushforward (complementaryClosureι i)).obj
            (curveDualizingModule (complementaryClosureι i ≫ X.hom))) ∧
      IsIsomorphic S.X₃ (complementaryIntersectionStructureSheaf i) := sorry

/-- The restricted sequence on the closed subscheme identifies its first and third objects with
the dualizing module and intersection structure sheaf. -/
theorem closedSubscheme_restrictedDualizing_objects :
    let S := sequence (idealOnClosedSubscheme i).subschemeι
      ((Modules.pullback i).obj (curveDualizingModule X.hom))
    IsIsomorphic S.X₁ (curveDualizingModule (i ≫ X.hom)) ∧
      IsIsomorphic S.X₃ (closedSubschemeStructureSheafOn (idealOnClosedSubscheme i)) := sorry

/-- The restricted sequence on the complementary closure identifies its first and third objects
with the dualizing module and intersection structure sheaf. -/
theorem complementaryClosure_restrictedDualizing_objects :
    let S := sequence (idealOnComplementaryClosure i).subschemeι
      ((Modules.pullback (complementaryClosureι i)).obj (curveDualizingModule X.hom))
    IsIsomorphic S.X₁ (curveDualizingModule (complementaryClosureι i ≫ X.hom)) ∧
      IsIsomorphic S.X₃ (closedSubschemeStructureSheafOn (idealOnComplementaryClosure i)) := sorry

/-- The first object of the Mayer--Vietoris row is the ambient dualizing module. -/
theorem dualizingMayerVietoris_left_isomorphic :
    let S := (schemeTheoreticUnionShortComplex i.ker (complementaryClosureι i).ker).map
      (tensorRight (curveDualizingModule X.hom))
    IsIsomorphic S.X₁ (curveDualizingModule X.hom) := sorry

/-- The middle object of the Mayer--Vietoris row is the biproduct of the two restricted modules. -/
theorem dualizingMayerVietoris_middle_isomorphic :
    let S := (schemeTheoreticUnionShortComplex i.ker (complementaryClosureι i).ker).map
      (tensorRight (curveDualizingModule X.hom))
    IsIsomorphic S.X₂
      ((Modules.pushforward i).obj ((Modules.pullback i).obj (curveDualizingModule X.hom)) ⊞
        (Modules.pushforward (complementaryClosureι i)).obj
          ((Modules.pullback (complementaryClosureι i)).obj (curveDualizingModule X.hom))) := sorry

/-- The third object of the Mayer--Vietoris row is the intersection structure sheaf. -/
theorem dualizingMayerVietoris_right_isomorphic :
    let S := (schemeTheoreticUnionShortComplex i.ker (complementaryClosureι i).ker).map
      (tensorRight (curveDualizingModule X.hom))
    IsIsomorphic S.X₃ (complementaryIntersectionStructureSheaf i) := sorry

/-- The first object of the complementary-closure ideal-tensor row is the pushforward of the
dualizing module of the closed subscheme. -/
theorem complementaryClosure_idealTensor_left_isomorphic :
    IsIsomorphic (sequence (complementaryClosureι i) (curveDualizingModule X.hom)).X₁
      ((Modules.pushforward i).obj (curveDualizingModule (i ≫ X.hom))) := sorry

/-- The first object of the closed-subscheme ideal-tensor row is the pushforward of the dualizing
module of the complementary closure. -/
theorem closedSubscheme_idealTensor_left_isomorphic :
    IsIsomorphic (sequence i (curveDualizingModule X.hom)).X₁
      ((Modules.pushforward (complementaryClosureι i)).obj
        (curveDualizingModule (complementaryClosureι i ≫ X.hom))) := sorry

end AlgebraicGeometry.Scheme

end
