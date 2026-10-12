/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.TorAmplitude

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek

/-- The degree-zero cohomology module of the compactification model of `f⁺!𝒪_Y`. -/
noncomputable abbrev dualizingModule
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)) :
    RingedSpace.Modules (LocallyRingedSpace.toRingedSpace
      (Scheme.toLocallyRingedSpace X.obj.left)) :=
  RingedSpace.ModuleDerived.cohomologySheaf (dualizingObject f P A).obj 0

/-- The degree-zero dualizing module of a flat quasi-finite morphism is coherent. -/
theorem dualizingModule_isCoherent
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [Flat f.hom.left] [Scheme.Hom.QuasiFinite f.hom.left]
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)) :
    (dualizingModule f P A).IsCoherent := sorry

/-- The degree-zero dualizing module of a flat quasi-finite morphism is flat over
the target. -/
theorem dualizingModule_isFlatOver
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [Flat f.hom.left] [Scheme.Hom.QuasiFinite f.hom.left]
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)) :
    SheafOfModules.IsFlatOver (dualizingModule f P A) f.hom.left.toShHom := sorry

/-- The compactification model of the dualizing object of a flat quasi-finite
morphism is its degree-zero cohomology module placed in degree zero. -/
theorem dualizingObject_isomorphic_single_dualizingModule
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [Flat f.hom.left] [Scheme.Hom.QuasiFinite f.hom.left]
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)) :
    IsIsomorphic (dualizingObject f P A).obj
      ((DerivedCategory.singleFunctor X.obj.left.Modules 0).obj (dualizingModule f P A)) := sorry

/-- A flat quasi-finite morphism has a coherent relative-flat dualizing module
whose degree-zero placement represents its compactification dualizing object. -/
theorem exists_dualizingModule_of_flat_quasiFinite
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [Flat f.hom.left] [Scheme.Hom.QuasiFinite f.hom.left]
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)) :
    ∃ ω : RingedSpace.Modules X.obj.left.toRingedSpace,
      ω.IsCoherent ∧
        SheafOfModules.IsFlatOver ω f.hom.left.toShHom ∧
          IsIsomorphic (dualizingObject f P A).obj
            ((DerivedCategory.singleFunctor X.obj.left.Modules 0).obj ω) := sorry

end AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek
