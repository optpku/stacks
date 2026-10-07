module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ProjectionFormula.ExtComparison
public import ReasLib.CategoryTheory.Monoidal.Closed.Triangulated

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalClosed
open RingedSpace.Module.Derived RingedSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace ModuleDerived
namespace ProjectionFormula

/-- The canonical ambient left-tensor functor inherits shift compatibility from the
fixed-right derived tensor model. -/
noncomputable instance tensorLeftCommShift (X : Scheme.{u})
    [h_homotopy : KFlat.HomotopyTensorDescends X.toRingedSpace]
    [h_tensor : KFlat.TensorDescends X.toRingedSpace]
    [h_localization : KFlat.IsLocalization X.toRingedSpace]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    (@MonoidalCategory.tensorLeft _ _
      (RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace) E).CommShift ℤ :=
  Functor.CommShift.ofIso
    (BraidedCategory.tensorLeftIsoTensorRight E ≪≫
      DerivedTensor.Right.Monoidal.tensorRightIsoFunctorOf E
        (@kFlatTensorCounit X (hasKFlatResolutions X) h_homotopy h_tensor h_tensor
          h_localization h_localization E)
        (@kFlatTensorCounit_isLeftDerived X (hasKFlatResolutions X) h_homotopy h_tensor h_tensor
          h_localization h_localization (homotopyLocalization_isLocalization X) E)).symm ℤ

/-- The canonical ambient left-tensor functor is triangulated exact. -/
noncomputable instance tensorLeftIsTriangulated (X : Scheme.{u})
    [h_homotopy : KFlat.HomotopyTensorDescends X.toRingedSpace]
    [h_tensor : KFlat.TensorDescends X.toRingedSpace]
    [h_localization : KFlat.IsLocalization X.toRingedSpace]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    (@MonoidalCategory.tensorLeft _ _
      (RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace) E).IsTriangulated := sorry

/-- The Ext delta functor in the coefficient variable, with value
`F ↦ RΓ(X, RHom(E, Q(G ⊗ f^*F)))`. -/
noncomputable def extDelta {X S : Scheme.{u}} (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)] :
    DeltaFunctor S.Modules (DerivedCategory AddCommGrpCat.{u}) :=
  let H := (ihom E : RingedSpace.ModuleDerived X.toRingedSpace ⥤
    RingedSpace.ModuleDerived X.toRingedSpace)
  let hHComm : H.CommShift ℤ := (ihom.adjunction E).rightAdjointCommShift ℤ
  let hHTri : H.IsTriangulatedWith hHComm :=
    (ihom.adjunction E).isTriangulatedWith_rightAdjoint
  DeltaFunctor.postcomposeExactFunctor
    (DeltaFunctor.postcomposeExactFunctor
      (@DeltaFunctor.postcomposeExactFunctor
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (((DerivedCategory.Delta.functor X.Modules).precomposeExactFunctor
          (coefficientComplexExactFunctor f G)) :
            DeltaFunctor S.Modules (RingedSpace.ModuleDerived X.toRingedSpace))
        H hHComm hHTri)
      (RingedSpace.moduleDerivedGlobalSections X.toRingedSpace))
    (forget₂ (ModuleCat X.toRingedSpace.globalSectionsRing) AddCommGrpCat.{u}).mapDerivedCategory

/-- Evaluation of `extDelta` is the derived-global-sections model of Ext against `E`. -/
theorem extDelta_obj {X S : Scheme.{u}} (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (F : S.Modules) :
    (extDelta f E G).obj F =
      (GlobalSections.toAbelian X.toRingedSpace).obj
        ((ihom E).obj (DerivedCategory.Q.obj (coefficientComplex f G F))) := sorry

/-- The delta functor representing `F ↦ Ext_S(L, F)`. -/
noncomputable def representedExtDelta (S : Scheme.{u})
    (L : RingedSpace.ModuleDerived S.toRingedSpace)
    [KFlat.HomotopyTensorDescends S.toRingedSpace]
    [KFlat.TensorDescends S.toRingedSpace]
    [KFlat.IsLocalization S.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)] :
    DeltaFunctor S.Modules (DerivedCategory AddCommGrpCat.{u}) :=
  let H := (ihom L : RingedSpace.ModuleDerived S.toRingedSpace ⥤
    RingedSpace.ModuleDerived S.toRingedSpace)
  let hHComm : H.CommShift ℤ := (ihom.adjunction L).rightAdjointCommShift ℤ
  let hHTri : H.IsTriangulatedWith hHComm :=
    (ihom.adjunction L).isTriangulatedWith_rightAdjoint
  DeltaFunctor.postcomposeExactFunctor
    (DeltaFunctor.postcomposeExactFunctor
      (@DeltaFunctor.postcomposeExactFunctor
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (GlobalSections.Delta.single S.toRingedSpace) H hHComm hHTri)
      (RingedSpace.moduleDerivedGlobalSections S.toRingedSpace))
    (forget₂ (ModuleCat S.toRingedSpace.globalSectionsRing) AddCommGrpCat.{u}).mapDerivedCategory

/-- Evaluation of `representedExtDelta` is the derived-global-sections model of
`Ext_S(L, F)`. -/
theorem representedExtDelta_obj (S : Scheme.{u})
    (L : RingedSpace.ModuleDerived S.toRingedSpace)
    [KFlat.HomotopyTensorDescends S.toRingedSpace]
    [KFlat.TensorDescends S.toRingedSpace]
    [KFlat.IsLocalization S.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)]
    (F : S.Modules) :
    (representedExtDelta S L).obj F =
      (GlobalSections.toAbelian S.toRingedSpace).obj
        ((ihom L).obj ((DerivedCategory.singleFunctor S.Modules 0).obj F)) := sorry

/-- The tensor-cohomology delta functor with value
`F ↦ RΓ(S, F[0] ⊗ᴸ K)`. -/
noncomputable def tensorDelta (S : Scheme.{u})
    (K : RingedSpace.ModuleDerived S.toRingedSpace)
    [KFlat.HomotopyTensorDescends S.toRingedSpace]
    [KFlat.TensorDescends S.toRingedSpace]
    [KFlat.IsLocalization S.toRingedSpace] :
    DeltaFunctor S.Modules (DerivedCategory AddCommGrpCat.{u}) :=
  DeltaFunctor.postcomposeExactFunctor
    (DeltaFunctor.postcomposeExactFunctor
      (postcomposeRightTensor S K (GlobalSections.Delta.single S.toRingedSpace))
      (RingedSpace.moduleDerivedGlobalSections S.toRingedSpace))
    (forget₂ (ModuleCat S.toRingedSpace.globalSectionsRing) AddCommGrpCat.{u}).mapDerivedCategory

/-- Evaluation of `tensorDelta` gives derived global sections of the symmetric
presentation `F[0] ⊗ᴸ K` of `K ⊗ᴸ F[0]`. -/
theorem tensorDelta_obj (S : Scheme.{u})
    (K : RingedSpace.ModuleDerived S.toRingedSpace)
    [KFlat.HomotopyTensorDescends S.toRingedSpace]
    [KFlat.TensorDescends S.toRingedSpace]
    [KFlat.IsLocalization S.toRingedSpace]
    (F : S.Modules) :
    (tensorDelta S K).obj F =
      (GlobalSections.toAbelian S.toRingedSpace).obj
        (DerivedTensor.Right.obj
          ((DerivedCategory.singleFunctor S.Modules 0).obj F) K) := sorry

/-- Degree-`i` cohomology of a derived-valued delta functor, restricted to
quasicoherent coefficient modules. -/
noncomputable def qcCohomology {S : Scheme.{u}}
    (D : DeltaFunctor S.Modules (DerivedCategory AddCommGrpCat.{u})) (i : ℤ) :
    Scheme.QCoh S ⥤ AddCommGrpCat.{u} :=
  Scheme.QCoh.inclusion S ⋙ D.toFunctor ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{u} i

/-- Evaluation of `qcCohomology` is homology of the delta-functor value on the
underlying quasicoherent module. -/
theorem qcCohomology_obj {S : Scheme.{u}}
    (D : DeltaFunctor S.Modules (DerivedCategory AddCommGrpCat.{u}))
    (i : ℤ) (F : Scheme.QCoh S) :
    (qcCohomology D i).obj F =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj (D.obj F.obj) := sorry

/-- An integer-graded natural transformation on quasicoherent coefficients that
commutes with the connecting maps of short exact sequences. -/
structure CohomologyTransform {S : Scheme.{u}}
    (D₁ D₂ : DeltaFunctor S.Modules (DerivedCategory AddCommGrpCat.{u})) where
  /-- The natural transformation in cohomological degree `i`. -/
  app (i : ℤ) : qcCohomology D₁ i ⟶ qcCohomology D₂ i
  /-- Compatibility of the degreewise transformations with connecting maps. -/
  boundary (T : ShortComplex S.Modules) (hT : T.ShortExact)
      (hT₁ : T.X₁.IsQuasicoherent) (hT₂ : T.X₂.IsQuasicoherent)
      (hT₃ : T.X₃.IsQuasicoherent) (i : ℤ) :
    CommSq ((app i).app ⟨T.X₃, hT₃⟩) (boundaryMap D₁ hT i)
      (boundaryMap D₂ hT i) ((app (i + 1)).app ⟨T.X₁, hT₁⟩)

/-- The degreewise natural transformation induced by a morphism of delta functors. -/
noncomputable def CohomologyTransform.ofDeltaHomApp {S : Scheme.{u}}
    {D₁ D₂ : DeltaFunctor S.Modules (DerivedCategory AddCommGrpCat.{u})}
    (c : D₁ ⟶ D₂) (i : ℤ) : qcCohomology D₁ i ⟶ qcCohomology D₂ i :=
  Functor.whiskerLeft (Scheme.QCoh.inclusion S)
    (Functor.whiskerRight c.app (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i))

/-- The transformations induced by a delta-functor morphism commute with boundary maps. -/
theorem CohomologyTransform.ofDeltaHomApp_boundary {S : Scheme.{u}}
    {D₁ D₂ : DeltaFunctor S.Modules (DerivedCategory AddCommGrpCat.{u})}
    (c : D₁ ⟶ D₂) (T : ShortComplex S.Modules) (hT : T.ShortExact)
    (hT₁ : T.X₁.IsQuasicoherent) (hT₂ : T.X₂.IsQuasicoherent)
    (hT₃ : T.X₃.IsQuasicoherent) (i : ℤ) :
    CommSq ((ofDeltaHomApp c i).app ⟨T.X₃, hT₃⟩) (boundaryMap D₁ hT i)
      (boundaryMap D₂ hT i) ((ofDeltaHomApp c (i + 1)).app ⟨T.X₁, hT₁⟩) := sorry

/-- A morphism of delta functors induces a boundary-compatible cohomology transform. -/
noncomputable def CohomologyTransform.ofDeltaHom {S : Scheme.{u}}
    {D₁ D₂ : DeltaFunctor S.Modules (DerivedCategory AddCommGrpCat.{u})}
    (c : D₁ ⟶ D₂) : CohomologyTransform D₁ D₂ where
  app := ofDeltaHomApp c
  boundary := ofDeltaHomApp_boundary c

/-- The degree-`i` map of `CohomologyTransform.ofDeltaHom c` is obtained by
whiskering `c.app` and applying degree-`i` homology. -/
theorem CohomologyTransform.ofDeltaHom_app {S : Scheme.{u}}
    {D₁ D₂ : DeltaFunctor S.Modules (DerivedCategory AddCommGrpCat.{u})}
    (c : D₁ ⟶ D₂) (i : ℤ) :
    (CohomologyTransform.ofDeltaHom c).app i = ofDeltaHomApp c i := sorry

end ProjectionFormula
end ModuleDerived
end Scheme
end AlgebraicGeometry
