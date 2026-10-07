module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Derived
public import ReasLib.CategoryTheory.Sites.Cech.Precomp
public import ReasLib.CategoryTheory.Sites.Cech.Refinement
public import ReasLib.Topology.Opens.Instances
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cech maps associated to morphisms of ringed spaces

An `f`-map followed by a refinement induces a concrete morphism of Cech complexes.  The
pushforward-to-preimage comparison is kept as a natural isomorphism, so the resulting datum does
not depend on transporting along an unproved equality of complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCech

variable {X Y : RingedSpace.{u}}

/-- Forgetting the scalar structure of a pushed-forward module sheaf agrees with pushing forward
its underlying additive presheaf. -/
@[stacks 01FD "underlying presheaf of a direct image"]
noncomputable def underlyingPresheafPushforwardIso (f : X ⟶ Y) :
    RingedSpace.Hom.pushforward f ⋙ moduleUnderlyingPresheaf Y ≅
      moduleUnderlyingPresheaf X ⋙
        TopCat.Presheaf.pushforward AddCommGrpCat.{u} f.hom.base :=
  Iso.refl _

/-- Cech complexes of a pushed-forward module on `Y` are canonically identified with Cech
complexes on `X` for the inverse-image family. -/
@[stacks 01FD "Cech complexes and direct image"]
noncomputable def pushforwardComplexIso
    (f : X ⟶ Y) {J : Type u} (V : J → Opens Y.carrier) :
    RingedSpace.Hom.pushforward f ⋙ moduleCechComplexFunctor V ≅
      moduleCechComplexFunctor (fun j ↦ preimageOpen f (V j)) :=
  (Functor.associator
      (RingedSpace.Hom.pushforward f) (moduleUnderlyingPresheaf Y)
      (cechComplexFunctor V)).symm ≪≫
    Functor.isoWhiskerRight (underlyingPresheafPushforwardIso f)
      (cechComplexFunctor V) ≪≫
    Functor.associator
      (moduleUnderlyingPresheaf X)
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f.hom.base)
      (cechComplexFunctor V) ≪≫
    Functor.isoWhiskerLeft (moduleUnderlyingPresheaf X)
      (Cech.Precomp.complexIso (A := AddCommGrpCat.{u}) (Opens.map f.hom.base) V)

namespace FMap

/-- The concrete Cech-complex map induced by an `f`-map and a fixed refinement of the source
cover by the inverse-image cover. -/
@[stacks 01FD "Cech complex map of an f-map and refinement"]
noncomputable def complexMap
    (f : X ⟶ Y) {I J : Type u}
    (U : I → Opens X.carrier) (V : J → Opens Y.carrier)
    (c : I → J) (hc : IsRefinement (fun j ↦ preimageOpen f (V j)) U c)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) :
    moduleCechComplex V G ⟶ moduleCechComplex U F :=
  (moduleCechComplexFunctor V).map φ ≫
    (pushforwardComplexIso f V).hom.app F ≫
    (cechRefinementNatTrans (fun j ↦ preimageOpen f (V j)) U c hc).app
      ((moduleUnderlyingPresheaf X).obj F)

/-- Localizing the concrete Cech-complex map associated to an `f`-map and a refinement. -/
@[stacks 01FD "derived Cech map of an f-map and refinement"]
noncomputable def derivedMap
    (f : X ⟶ Y) {I J : Type u}
    (U : I → Opens X.carrier) (V : J → Opens Y.carrier)
    (c : I → J) (hc : IsRefinement (fun j ↦ preimageOpen f (V j)) U c)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) :
    (derivedFunctor V).obj G ⟶ (derivedFunctor U).obj F :=
  (DerivedCategory.Plus.ι :
      DerivedCategory.Plus AddCommGrpCat.{u} ⥤ DerivedCategory AddCommGrpCat.{u}).map
    ((DerivedCategory.Plus.Q :
        CochainComplex.Plus AddCommGrpCat.{u} ⥤
          DerivedCategory.Plus AddCommGrpCat.{u}).map
      ((CochainComplex.Plus.extendNat AddCommGrpCat.{u}).map
        (complexMap f U V c hc φ)))

/-- The derived `f`-map is the image of `complexMap` under extension by zero and the two
localization functors. -/
@[stacks 01FD "derived Cech map realization"]
theorem derivedMap_eq
    (f : X ⟶ Y) {I J : Type u}
    (U : I → Opens X.carrier) (V : J → Opens Y.carrier)
    (c : I → J) (hc : IsRefinement (fun j ↦ preimageOpen f (V j)) U c)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) :
    derivedMap f U V c hc φ =
      (DerivedCategory.Plus.ι :
          DerivedCategory.Plus AddCommGrpCat.{u} ⥤ DerivedCategory AddCommGrpCat.{u}).map
        ((DerivedCategory.Plus.Q :
            CochainComplex.Plus AddCommGrpCat.{u} ⥤
              DerivedCategory.Plus AddCommGrpCat.{u}).map
          ((CochainComplex.Plus.extendNat AddCommGrpCat.{u}).map
            (complexMap f U V c hc φ))) := sorry

/-- The map induced on Cech cohomology by the concrete complex map associated to an `f`-map and
a refinement. -/
@[stacks 01FD "Cech cohomology map of an f-map and refinement"]
noncomputable def cohomologyMap
    (f : X ⟶ Y) {I J : Type u}
    (U : I → Opens X.carrier) (V : J → Opens Y.carrier)
    (c : I → J) (hc : IsRefinement (fun j ↦ preimageOpen f (V j)) U c)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) (p : ℕ) :
    moduleCechCohomology V G p ⟶ moduleCechCohomology U F p :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
    (complexMap f U V c hc φ)

/-- The cohomology-level `f`-map is obtained by applying the homology functor to `complexMap`. -/
@[stacks 01FD "Cech cohomology map realization"]
theorem cohomologyMap_eq
    (f : X ⟶ Y) {I J : Type u}
    (U : I → Opens X.carrier) (V : J → Opens Y.carrier)
    (c : I → J) (hc : IsRefinement (fun j ↦ preimageOpen f (V j)) U c)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) (p : ℕ) :
    cohomologyMap f U V c hc φ p =
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
        (complexMap f U V c hc φ) := sorry

end FMap

end AlgebraicGeometry.RingedSpace.ModuleCech
