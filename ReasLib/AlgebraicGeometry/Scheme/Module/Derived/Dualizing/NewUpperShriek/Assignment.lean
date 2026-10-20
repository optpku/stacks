/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.OppositeLocallyDiscrete
public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeOver.Base
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.Relative

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.Bicategory DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace CategoryTheory.Functor

/-- The functor on homotopy categories induced by the identity functor is canonically
isomorphic to the identity functor. -/
noncomputable def mapHomotopyCategoryIdIso (A : Type u) [Category A] [Preadditive A] :
    (𝟭 A).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      𝟭 (HomotopyCategory A (ComplexShape.up ℤ)) :=
  Quotient.natIsoLift _
    (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ))
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)))

end CategoryTheory.Functor

namespace AlgebraicGeometry.RingedSpace.modulePullbackDerived

/-- The homotopy-level identity-pullback model is canonically isomorphic to the
derived localization functor. -/
noncomputable def idSourceIso (X : RingedSpace.{u}) :
    modulePullbackToDerived (𝟙 X) ≅
      (DerivedCategory.Qh : HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤
        X.ModuleDerived) :=
  Functor.isoWhiskerRight
      ((Functor.mapHomotopyCategoryIso (RingedSpace.Hom.pullbackIdIso X)) ≪≫
        Functor.mapHomotopyCategoryIdIso X.Modules)
      (DerivedCategory.Qh : HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤
        X.ModuleDerived) ≪≫
    Functor.leftUnitor _

/-- The canonical counit presenting the identity of `X.ModuleDerived` as a left-derived
model of pullback along `𝟙 X`. -/
noncomputable def idCounit (X : RingedSpace.{u}) :
    (DerivedCategory.Qh : HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤
        X.ModuleDerived) ⋙
        Functor.id X.ModuleDerived ⟶ modulePullbackToDerived (𝟙 X) :=
  (Functor.rightUnitor _).hom ≫ (idSourceIso X).inv

/-- The identity functor with `idCounit` has the canonical left-derived universal property. -/
instance idFunctorIsLeftDerived (X : RingedSpace.{u}) :
    (Functor.id X.ModuleDerived).IsLeftDerivedFunctor
      (idCounit X) (RingedSpace.ModuleQis X) := sorry

/-- Derived pullback along the identity is canonically isomorphic to the identity functor. -/
noncomputable def idIso (X : RingedSpace.{u}) :
    modulePullbackDerived (𝟙 X) ≅ Functor.id X.ModuleDerived :=
  Functor.leftDerivedNatIso
    (modulePullbackDerived (𝟙 X)) (Functor.id X.ModuleDerived)
    ((modulePullbackToDerived (𝟙 X)).totalLeftDerivedCounit
      DerivedCategory.Qh (RingedSpace.ModuleQis X))
    (idCounit X) (RingedSpace.ModuleQis X) (Iso.refl _)

end AlgebraicGeometry.RingedSpace.modulePullbackDerived

namespace AlgebraicGeometry.Scheme

namespace DerivedCoh

/-- The bounded-below derived category of modules with coherent cohomology on `X`. -/
abbrev Plus (X : Scheme.{u}) :=
  D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf]

/-- `DerivedCoh.Plus X` is the canonical bounded-below coherent full subcategory. -/
theorem plus_eq (X : Scheme.{u}) :
    Plus X = D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf] := sorry

end DerivedCoh

/-- An explicit family of complexes normalized relative to the fixed dualizing complex
`ωS` from Situation 48.20.1.

Only the normalized family, the K-flat construction hypotheses, and the compatible closed
structures are choice data. The new-upper-shriek functors and their pseudofunctor structure are
derived from this data. -/
structure NewUpperShriekAssignment (S : Scheme.{u}) [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    (H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
    (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex H) where
  /-- Tensoring descends from complexes to the homotopy category. -/
  homotopyTensorDescends (X : FiniteTypeOver S) :
    RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.obj.left.toRingedSpace
  /-- Tensoring K-flat objects preserves the quasi-isomorphisms being localized. -/
  tensorDescends (X : FiniteTypeOver S) :
    @RingedSpace.ModuleDerived.KFlat.TensorDescends X.obj.left.toRingedSpace
      (homotopyTensorDescends X)
  /-- K-flat objects give the standard localization model of the derived category. -/
  isLocalization (X : FiniteTypeOver S) :
    RingedSpace.ModuleDerived.KFlat.IsLocalization X.obj.left.toRingedSpace
  /-- The chosen closed structure is based on the canonical K-flat monoidal structure. -/
  closed (X : FiniteTypeOver S) :
    @MonoidalClosed (RingedSpace.ModuleDerived X.obj.left.toRingedSpace) _
      (@RingedSpace.ModuleDerived.monoidalCategory X.obj.left.toRingedSpace
        (homotopyTensorDescends X) (tensorDescends X) (isLocalization X))
  /-- The chosen normalized bounded-below coherent complex on every finite-type `S`-scheme. -/
  omega (X : FiniteTypeOver S) : DerivedCoh.Plus X.obj.left
  /-- Every member of the family is normalized relative to the fixed complex `ωS`. -/
  normalized (X : FiniteTypeOver S) :
    @Hom.NormalizedDualizingComplex.RelativeTo S X.obj.left _ X.obj.hom
      (FiniteTypeOver.instFiniteType X) inferInstance H
      (@RingedSpace.ModuleDerived.monoidalCategory X.obj.left.toRingedSpace
        (homotopyTensorDescends X) (tensorDescends X) (isLocalization X)) (closed X)
      ωS hωS (omega X).obj.obj
  /-- At the base object, the chosen normalized family recovers the fixed `ωS`. -/
  baseComparison :
    IsIsomorphic (omega (FiniteTypeOver.base S)).obj.obj ωS

namespace NewUpperShriekAssignment

/-- The canonical K-flat monoidal structure selected by an assignment. -/
noncomputable abbrev monoidal {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS) (X : FiniteTypeOver S) :
    MonoidalCategory (RingedSpace.ModuleDerived X.obj.left.toRingedSpace) :=
  @RingedSpace.ModuleDerived.monoidalCategory X.obj.left.toRingedSpace
    (D.homotopyTensorDescends X) (D.tensorDescends X) (D.isLocalization X)

/-- The canonical K-flat braiding selected by an assignment. -/
noncomputable abbrev braided {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS) (X : FiniteTypeOver S) :
    @BraidedCategory (RingedSpace.ModuleDerived X.obj.left.toRingedSpace) _ (D.monoidal X) :=
  (@RingedSpace.ModuleDerived.symmetricCategory X.obj.left.toRingedSpace
    (D.homotopyTensorDescends X) (D.tensorDescends X) (D.isLocalization X)).toBraidedCategory

/-- Construct a new-upper-shriek assignment from an explicit family normalized relative to
the fixed Situation 48.20.1 data. -/
def ofNormalized {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    (H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
    (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex H)
    (homotopyTensorDescends : ∀ X : FiniteTypeOver S,
      RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.obj.left.toRingedSpace)
    (tensorDescends : ∀ X : FiniteTypeOver S,
      @RingedSpace.ModuleDerived.KFlat.TensorDescends X.obj.left.toRingedSpace
        (homotopyTensorDescends X))
    (isLocalization : ∀ X : FiniteTypeOver S,
      RingedSpace.ModuleDerived.KFlat.IsLocalization X.obj.left.toRingedSpace)
    (closed : ∀ X : FiniteTypeOver S,
      @MonoidalClosed (RingedSpace.ModuleDerived X.obj.left.toRingedSpace) _
        (@RingedSpace.ModuleDerived.monoidalCategory X.obj.left.toRingedSpace
          (homotopyTensorDescends X) (tensorDescends X) (isLocalization X)))
    (omega : ∀ X : FiniteTypeOver S, DerivedCoh.Plus X.obj.left)
    (normalized : ∀ X : FiniteTypeOver S,
      @Hom.NormalizedDualizingComplex.RelativeTo S X.obj.left _ X.obj.hom
        (FiniteTypeOver.instFiniteType X) inferInstance H
        (@RingedSpace.ModuleDerived.monoidalCategory X.obj.left.toRingedSpace
          (homotopyTensorDescends X) (tensorDescends X) (isLocalization X)) (closed X)
        ωS hωS (omega X).obj.obj)
    (baseComparison : IsIsomorphic (omega (FiniteTypeOver.base S)).obj.obj ωS) :
    NewUpperShriekAssignment S H ωS hωS where
  homotopyTensorDescends := homotopyTensorDescends
  tensorDescends := tensorDescends
  isLocalization := isLocalization
  closed := closed
  omega := omega
  normalized := normalized
  baseComparison := baseComparison

variable {S : Scheme.{u}} [IsNoetherian S]
variable [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
variable {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
variable {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}

/-- Every chosen normalized member is dualizing in the scheme-local sense. -/
theorem dualizing (D : NewUpperShriekAssignment S H ωS hωS) (X : FiniteTypeOver S) :
    Scheme.IsDualizingComplex (D.omega X).obj.obj := sorry

/-- Every chosen normalized member is dualizing for the explicit closed structure used by
new upper shriek. -/
theorem moduleDualizing (D : NewUpperShriekAssignment S H ωS hωS)
    (X : FiniteTypeOver S) :
    @RingedSpace.ModuleDerived.IsDualizingComplex X.obj.left.toRingedSpace
      (D.omega X).obj.obj (D.monoidal X) (D.closed X) := sorry

/-- The exceptional inverse-image functor assigned to `f` is exactly the existing
duality-pullback-duality construction. -/
noncomputable def map (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y) :
    DerivedCoh.Plus Y.obj.left ⥤ DerivedCoh.Plus X.obj.left :=
  @Hom.NewUpperShriek.functor X.obj.left Y.obj.left f.hom.left
    (FiniteTypeOver.instFiniteTypeHom f) (D.monoidal X) (D.braided X) (D.closed X)
    (D.monoidal Y) (D.braided Y) (D.closed Y) (D.omega X).obj.obj (D.omega Y).obj.obj
    (D.moduleDualizing X) (D.moduleDualizing Y)

/-- The explicit duality functor used in the definition of new upper shriek on `X`. -/
noncomputable def dual (D : NewUpperShriekAssignment S H ωS hωS)
    (X : FiniteTypeOver S) :
    (RingedSpace.ModuleDerived X.obj.left.toRingedSpace)ᵒᵖ ⥤
      RingedSpace.ModuleDerived X.obj.left.toRingedSpace :=
  @RightInternalHom.dualFunctor
    (RingedSpace.ModuleDerived X.obj.left.toRingedSpace) _ (D.monoidal X)
    (@RightInternalHom.ofBraidedClosedOf
      (RingedSpace.ModuleDerived X.obj.left.toRingedSpace) _
      (D.monoidal X) (D.braided X) (D.closed X)) (D.omega X).obj.obj

/-- A coherent complex, regarded as an ambient derived object, has the canonical
biduality isomorphism associated to the normalized complex on `X`. -/
noncomputable def coherentBidualIso (D : NewUpperShriekAssignment S H ωS hωS)
    (X : FiniteTypeOver S)
    (K : D[SheafOfModules.isCoherent X.obj.left.toRingedSpace.ringCatSheaf]) :
    K.obj ≅ (D.dual X).obj (Opposite.op ((D.dual X).obj (Opposite.op K.obj))) :=
  (DerivedCategory.cohomologyIn
    (SheafOfModules.isCoherent X.obj.left.toRingedSpace.ringCatSheaf)).ι.mapIso
    ((@asIso _ _ _ _
      (@Scheme.IsDualizingComplex.coherentBidual X.obj.left inferInstance
        (D.monoidal X) (D.braided X) (D.closed X) (D.omega X).obj.obj
        (D.dualizing X))
      (@Scheme.IsDualizingComplex.coherentBidualIsIso X.obj.left inferInstance
        (D.monoidal X) (D.braided X) (D.closed X) (D.omega X).obj.obj
        (D.dualizing X))).app K)

/-- Duality against the normalized complex selected by `D` is involutive on complexes
with coherent cohomology on `X`. -/
theorem coherentDualityInvolutive (D : NewUpperShriekAssignment S H ωS hωS)
    (X : FiniteTypeOver S) :
    IsIso (@Scheme.IsDualizingComplex.coherentBidual X.obj.left inferInstance
      (D.monoidal X) (D.braided X) (D.closed X) (D.omega X).obj.obj
      (D.dualizing X)) := sorry

/-- Duality against the normalized complex selected by `D` exchanges bounded-below and
bounded-above complexes with coherent cohomology on `X`. -/
theorem plusDualityIsEquivalence (D : NewUpperShriekAssignment S H ωS hωS)
    (X : FiniteTypeOver S) :
    (@Scheme.IsDualizingComplex.plusDuality X.obj.left inferInstance
      (D.monoidal X) (D.braided X) (D.closed X) (D.omega X).obj.obj
      (D.dualizing X) inferInstance).IsEquivalence := sorry

/-- Duality against the normalized complex selected by `D` is an anti-equivalence of
bounded complexes with coherent cohomology on `X`. -/
theorem boundedDualityIsEquivalence (D : NewUpperShriekAssignment S H ωS hωS)
    (X : FiniteTypeOver S) :
    (@Scheme.IsDualizingComplex.boundedDuality X.obj.left inferInstance
      (D.monoidal X) (D.braided X) (D.closed X) (D.omega X).obj.obj
      (D.dualizing X) inferInstance).IsEquivalence := sorry

/-- Forgetting boundedness and coherent cohomology from `map D f` gives the defining
duality-pullback-duality formula. -/
theorem map_obj_obj (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y) (K : DerivedCoh.Plus Y.obj.left) :
    ((D.map f).obj K).obj.obj =
      (@MonoidalClosed.ihomOf _ _ (D.monoidal X) (D.closed X)
        ((RingedSpace.modulePullbackDerived f.hom.left.toShHom).obj
          ((@MonoidalClosed.ihomOf _ _ (D.monoidal Y) (D.closed Y) K.obj.obj).obj
            (D.omega Y).obj.obj))).obj (D.omega X).obj.obj := sorry

/-- The action on an arrow of the opposite category, as a morphism in `Cat`. -/
noncomputable def mapCat {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : (FiniteTypeOver S)ᵒᵖ} (f : X ⟶ Y) :
    Cat.of (DerivedCoh.Plus X.unop.obj.left) ⟶ Cat.of (DerivedCoh.Plus Y.unop.obj.left) :=
  (D.map f.unop).toCatHom

/-- The functor underlying `mapCat D f` is the selected new-upper-shriek functor. -/
theorem mapCat_toFunctor {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : (FiniteTypeOver S)ᵒᵖ} (f : X ⟶ Y) :
    (D.mapCat f).toFunctor = D.map f.unop := sorry

/-- The underlying coherent object of a bounded-below coherent complex. -/
def coherentOfPlus (X : FiniteTypeOver S) (K : DerivedCoh.Plus X.obj.left) :
    D[SheafOfModules.isCoherent X.obj.left.toRingedSpace.ringCatSheaf] :=
  ⟨K.obj.obj, K.property⟩

/-- Pullback of the dual of a bounded-below coherent complex along a finite-type map has
coherent cohomology. -/
theorem pullbackDual_coherent (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y) (K : DerivedCoh.Plus Y.obj.left) :
    DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.obj.left.toRingedSpace.ringCatSheaf)
      ((RingedSpace.modulePullbackDerived f.hom.left.toShHom).obj
        ((D.dual Y).obj (Opposite.op K.obj.obj))) := sorry

/-- The pullback of the dual of `K`, packaged with its coherent cohomology. -/
def pullbackDualCoherent (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y) (K : DerivedCoh.Plus Y.obj.left) :
    D[SheafOfModules.isCoherent X.obj.left.toRingedSpace.ringCatSheaf] :=
  ⟨(RingedSpace.modulePullbackDerived f.hom.left.toShHom).obj
      ((D.dual Y).obj (Opposite.op K.obj.obj)), D.pullbackDual_coherent f K⟩

/-- The source's identity comparison, obtained by applying duality to the inverse of the
canonical identity-pullback comparison and then applying inverse biduality. -/
noncomputable def mapIdHom (D : NewUpperShriekAssignment S H ωS hωS)
    (X : FiniteTypeOver S) :
    D.map (𝟙 X) ⟶ Functor.id (DerivedCoh.Plus X.obj.left) where
  app K := ObjectProperty.homMk (ObjectProperty.homMk
    ((D.dual X).map (Opposite.op
      ((RingedSpace.modulePullbackDerived.idIso X.obj.left.toRingedSpace).inv.app
        ((D.dual X).obj (Opposite.op K.obj.obj)))) ≫
      (D.coherentBidualIso X (coherentOfPlus X K)).inv))
  naturality := sorry

/-- The identity comparison is invertible. -/
theorem mapIdHom_isIso (D : NewUpperShriekAssignment S H ωS hωS)
    (X : FiniteTypeOver S) : IsIso (D.mapIdHom X) := sorry

/-- The explicit reverse identity comparison, obtained from biduality and the canonical
identity-pullback comparison. -/
noncomputable def mapIdInv (D : NewUpperShriekAssignment S H ωS hωS)
    (X : FiniteTypeOver S) :
    Functor.id (DerivedCoh.Plus X.obj.left) ⟶ D.map (𝟙 X) where
  app K := ObjectProperty.homMk (ObjectProperty.homMk
    ((D.coherentBidualIso X (coherentOfPlus X K)).hom ≫
      (D.dual X).map (Opposite.op
        ((RingedSpace.modulePullbackDerived.idIso X.obj.left.toRingedSpace).hom.app
          ((D.dual X).obj (Opposite.op K.obj.obj))))))
  naturality := sorry

/-- The canonical identity comparison for new upper shriek. -/
noncomputable def mapId (D : NewUpperShriekAssignment S H ωS hωS)
    (X : FiniteTypeOver S) :
    D.map (𝟙 X) ≅ Functor.id (DerivedCoh.Plus X.obj.left) where
  hom := D.mapIdHom X
  inv := D.mapIdInv X
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The ambient arrow inside the compositor: inverse biduality followed by the canonical
derived-pullback composition comparison. -/
noncomputable def mapCompInner (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y Z : FiniteTypeOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : DerivedCoh.Plus Z.obj.left) :
    (RingedSpace.modulePullbackDerived f.hom.left.toShHom).obj
        ((D.dual Y).obj (Opposite.op ((D.dual Y).obj (Opposite.op
          ((RingedSpace.modulePullbackDerived g.hom.left.toShHom).obj
            ((D.dual Z).obj (Opposite.op K.obj.obj))))))) ⟶
      (RingedSpace.modulePullbackDerived (f ≫ g).hom.left.toShHom).obj
        ((D.dual Z).obj (Opposite.op K.obj.obj)) :=
  (RingedSpace.modulePullbackDerived f.hom.left.toShHom).map
      (D.coherentBidualIso Y (D.pullbackDualCoherent g K)).inv ≫
    (RingedSpace.modulePullbackDerived.compComparison
      f.hom.left.toShHom g.hom.left.toShHom).app
        ((D.dual Z).obj (Opposite.op K.obj.obj))

/-- The explicit reverse of `mapCompInner`, obtained from the inverse derived-pullback
comparison followed by biduality. -/
noncomputable def mapCompInnerInv (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y Z : FiniteTypeOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : DerivedCoh.Plus Z.obj.left) :
    (RingedSpace.modulePullbackDerived (f ≫ g).hom.left.toShHom).obj
        ((D.dual Z).obj (Opposite.op K.obj.obj)) ⟶
      (RingedSpace.modulePullbackDerived f.hom.left.toShHom).obj
        ((D.dual Y).obj (Opposite.op ((D.dual Y).obj (Opposite.op
          ((RingedSpace.modulePullbackDerived g.hom.left.toShHom).obj
            ((D.dual Z).obj (Opposite.op K.obj.obj))))))) :=
  (RingedSpace.modulePullbackDerived.compIso
      f.hom.left.toShHom g.hom.left.toShHom
      (RingedSpace.modulePullbackDerived.compComparison_isIso
        f.hom.left.toShHom g.hom.left.toShHom)).inv.app
          ((D.dual Z).obj (Opposite.op K.obj.obj)) ≫
    (RingedSpace.modulePullbackDerived f.hom.left.toShHom).map
      (D.coherentBidualIso Y (D.pullbackDualCoherent g K)).hom

/-- The source's composition arrow `(f ≫ g)⁺! ⟶ g⁺! ⋙ f⁺!`, obtained by
applying source duality to `mapCompInner`. -/
noncomputable def mapCompHom (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y Z : FiniteTypeOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    D.map (f ≫ g) ⟶ D.map g ⋙ D.map f where
  app K := ObjectProperty.homMk (ObjectProperty.homMk
    ((D.dual X).map (Opposite.op (D.mapCompInner f g K))))
  naturality := sorry

/-- The explicit reverse composition comparison for new upper shriek. -/
noncomputable def mapCompInv (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y Z : FiniteTypeOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    D.map g ⋙ D.map f ⟶ D.map (f ≫ g) where
  app K := ObjectProperty.homMk (ObjectProperty.homMk
    ((D.dual X).map (Opposite.op (D.mapCompInnerInv f g K))))
  naturality := sorry

/-- The canonical composition arrow is invertible. -/
theorem mapCompHom_isIso (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y Z : FiniteTypeOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsIso (D.mapCompHom f g) := sorry

/-- The canonical composition comparison for new upper shriek. -/
noncomputable def mapComp (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y Z : FiniteTypeOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    D.map (f ≫ g) ≅ D.map g ⋙ D.map f where
  hom := D.mapCompHom f g
  inv := D.mapCompInv f g
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `mapId` is the canonical identity arrow built from identity pullback
and biduality. -/
theorem mapId_hom (D : NewUpperShriekAssignment S H ωS hωS)
    (X : FiniteTypeOver S) : (D.mapId X).hom = D.mapIdHom X := sorry

/-- The forward map of `mapComp` is the canonical arrow built from inverse biduality and the
derived-pullback composition comparison. -/
theorem mapComp_hom (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y Z : FiniteTypeOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (D.mapComp f g).hom = D.mapCompHom f g := sorry

/-- The canonical composition comparisons obey associativity. -/
theorem mapComp_assoc (D : NewUpperShriekAssignment S H ωS hωS)
    {X₀ X₁ X₂ X₃ : (FiniteTypeOver S)ᵒᵖ}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) :
    (Cat.Hom.isoMk (D.mapComp h.unop (f ≫ g).unop)).hom ≫
        (Cat.Hom.isoMk (D.mapComp g.unop f.unop)).hom ▷
          D.mapCat h ≫
      (α_ (D.mapCat f) (D.mapCat g) (D.mapCat h)).hom ≫
      D.mapCat f ◁
        (Cat.Hom.isoMk (D.mapComp h.unop g.unop)).inv ≫
      (Cat.Hom.isoMk (D.mapComp (g ≫ h).unop f.unop)).inv =
        eqToHom (congrArg D.mapCat (Category.assoc f g h)) := sorry

/-- The canonical comparisons obey the left-unit coherence equation. -/
theorem map₂_leftUnitor (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : (FiniteTypeOver S)ᵒᵖ} (f : X ⟶ Y) :
    (Cat.Hom.isoMk (D.mapComp f.unop (𝟙 X).unop)).hom ≫
        (Cat.Hom.isoMk (D.mapId (unop X))).hom ▷ D.mapCat f ≫
      (λ_ (D.mapCat f)).hom =
        eqToHom (congrArg D.mapCat (Category.id_comp f)) := sorry

/-- The canonical comparisons obey the right-unit coherence equation. -/
theorem map₂_rightUnitor (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : (FiniteTypeOver S)ᵒᵖ} (f : X ⟶ Y) :
    (Cat.Hom.isoMk (D.mapComp (𝟙 Y).unop f.unop)).hom ≫
        D.mapCat f ◁ (Cat.Hom.isoMk (D.mapId (unop Y))).hom ≫
      (ρ_ (D.mapCat f)).hom =
        eqToHom (congrArg D.mapCat (Category.comp_id f)) := sorry

/-- The contravariant `Cat`-valued pseudofunctor assembled directly from the source's
canonical identity and composition arrows. -/
noncomputable def pseudofunctor (D : NewUpperShriekAssignment S H ωS hωS) :
    LocallyDiscrete (FiniteTypeOver S)ᵒᵖ ⥤ᵖ Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of (DerivedCoh.Plus X.unop.obj.left))
    D.mapCat
    (fun X ↦ Cat.Hom.isoMk (D.mapId (unop X)))
    (fun f g ↦ Cat.Hom.isoMk (D.mapComp g.unop f.unop))
    D.mapComp_assoc D.map₂_leftUnitor D.map₂_rightUnitor

/-- The new-upper-shriek pseudofunctor takes `X` to `D⁺_Coh(𝒪_X)`. -/
theorem pseudofunctor_obj {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS) (X : FiniteTypeOver S) :
    D.pseudofunctor.obj (LocallyDiscrete.mk (op X)) =
      Cat.of (DerivedCoh.Plus X.obj.left) := sorry

/-- The new-upper-shriek pseudofunctor acts on `f` by the selected functor `D.map f`. -/
theorem pseudofunctor_map {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS) {X Y : FiniteTypeOver S} (f : X ⟶ Y) :
    (D.pseudofunctor.map f.op.toLoc).toFunctor = D.map f := sorry

/-- The unit comparison exposed by `mapId` is the unit comparison of `pseudofunctor`. -/
theorem mapId_eq {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS) (X : FiniteTypeOver S) :
    Cat.Hom.toNatIso (D.pseudofunctor.mapIdOp X) = D.mapId X := sorry

/-- The compositor exposed by `mapComp` is the compositor of `pseudofunctor`. -/
theorem mapComp_eq {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y Z : FiniteTypeOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Cat.Hom.toNatIso (D.pseudofunctor.mapCompOp g f) = D.mapComp f g := sorry

/-- The chosen normalized complex on `X` is the new upper shriek of the base complex. -/
theorem omega_isIsomorphic_mapToBase {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS) (X : FiniteTypeOver S) :
    IsIsomorphic (D.omega X) ((D.map (FiniteTypeOver.toBase X)).obj
      (D.omega (FiniteTypeOver.base S))) := sorry

/-- Normalized complexes are functorial under every morphism over `S`. -/
theorem omega_isIsomorphic_map {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y) :
    IsIsomorphic (D.omega X) ((D.map f).obj (D.omega Y)) := sorry

end NewUpperShriekAssignment

end AlgebraicGeometry.Scheme
