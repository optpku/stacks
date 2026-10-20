module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.SheafyTrace.Counterexample
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalClosed
open RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

#check (AlgebraicGeometry.Scheme.DerivedQCoh.affineLineTraceSourceMem :
    let Y := Spec (CommRingCat.of ℤ)
    let X := Spec (CommRingCat.of (Polynomial ℤ))
    let f : X ⟶ Y := Spec.map (CommRingCat.ofHom Polynomial.C)
    let L := AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf X
    let K := AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf Y
    ∀ [HomotopyTensorDescends X.toRingedSpace]
      [TensorDescends X.toRingedSpace]
      [IsLocalization X.toRingedSpace]
      [HomotopyTensorDescends Y.toRingedSpace]
      [TensorDescends Y.toRingedSpace]
      [IsLocalization Y.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
      [MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace)]
      [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
      [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
      (a : AlgebraicGeometry.Scheme.DerivedQCoh Y ⥤
        AlgebraicGeometry.Scheme.DerivedQCoh X)
      (adj : AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a),
      AlgebraicGeometry.Scheme.derivedQuasiCoherentModuleProperty Y
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
          ((ihom L.obj).obj (a.obj K).obj)))

#check (AlgebraicGeometry.Scheme.DerivedQCoh.affineLineTraceTargetIsoProduct :
    let Y := Spec (CommRingCat.of ℤ)
    let X := Spec (CommRingCat.of (Polynomial ℤ))
    let f : X ⟶ Y := Spec.map (CommRingCat.ofHom Polynomial.C)
    let L := AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf X
    let K := AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf Y
    ∀ [HomotopyTensorDescends Y.toRingedSpace]
      [TensorDescends Y.toRingedSpace]
      [IsLocalization Y.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace)],
      IsIsomorphic
        ((ihom
          ((RingedSpace.moduleDerivedPushforward f.toShHom).obj L.obj)).obj K.obj)
        (∏ᶜ fun _ : ℕ ↦ K.obj))

#check (AlgebraicGeometry.Scheme.DerivedQCoh.countableProductStructureSheafNotQuasicoherent :
    let Y := Spec (CommRingCat.of ℤ)
    let K := AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf Y
    ¬ AlgebraicGeometry.Scheme.derivedQuasiCoherentModuleProperty Y
      (∏ᶜ fun _ : ℕ ↦ K.obj))

/- Example 48.3.7: for the affine line over `ℤ`, with both inputs the corresponding
structure sheaves, the uncoherated sheafy trace comparison is not an isomorphism. -/
@[stacks 0GEU] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affineLineTraceMapNotIso :
    let Y := Spec (CommRingCat.of ℤ)
    let X := Spec (CommRingCat.of (Polynomial ℤ))
    let f : X ⟶ Y := Spec.map (CommRingCat.ofHom Polynomial.C)
    let L := AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf X
    let K := AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf Y
    ∀ [HomotopyTensorDescends X.toRingedSpace]
      [TensorDescends X.toRingedSpace]
      [IsLocalization X.toRingedSpace]
      [HomotopyTensorDescends Y.toRingedSpace]
      [TensorDescends Y.toRingedSpace]
      [IsLocalization Y.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
      [MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace)]
      [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
      [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
      (a : AlgebraicGeometry.Scheme.DerivedQCoh Y ⥤
        AlgebraicGeometry.Scheme.DerivedQCoh X)
      (adj : AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a),
      ¬ IsIso (AlgebraicGeometry.Scheme.DerivedQCoh.uncoheratedSheafyTraceMap
        f a adj L K))
