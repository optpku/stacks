/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalProperties
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction

/-!
# Properties of associated modules on standard sites

This module records the module properties preserved and reflected by the
associated-module equivalences on standard big and small scheme sites.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- The module properties preserved and reflected by associated modules on
standard sites without an additional Noetherian hypothesis. -/
structure Property where
  /-- The code of the selected property, with twelve unindexed choices and two
  indexed families. -/
  code : Fin 12 ⊕ (Bool × ℕ)

namespace Property

/-- Freeness. -/
def free : Property := ⟨.inl 0⟩

/-- Finite freeness. -/
def finiteFree : Property := ⟨.inl 1⟩

/-- Global generation. -/
def globallyGenerated : Property := ⟨.inl 2⟩

/-- Generation by a fixed finite number of global sections. -/
def generatedBy (r : ℕ) : Property := ⟨.inr (false, r)⟩

/-- Finite global generation. -/
def finiteGloballyGenerated : Property := ⟨.inl 3⟩

/-- Existence of a global presentation. -/
def globalPresentation : Property := ⟨.inl 4⟩

/-- Existence of a finite global presentation. -/
def finiteGlobalPresentation : Property := ⟨.inl 5⟩

/-- Finite local freeness. -/
def finiteLocallyFree : Property := ⟨.inl 6⟩

/-- Local generation by sections. -/
def locallyGenerated : Property := ⟨.inl 7⟩

/-- Local generation by a fixed finite number of sections. -/
def locallyGeneratedBy (r : ℕ) : Property := ⟨.inr (true, r)⟩

/-- Finite type. -/
def finiteType : Property := ⟨.inl 8⟩

/-- Quasi-coherence. -/
def quasicoherent : Property := ⟨.inl 9⟩

/-- Finite presentation. -/
def finitePresentation : Property := ⟨.inl 10⟩

/-- Flatness. -/
def flat : Property := ⟨.inl 11⟩

/-- Interpret an associated-module property on a quasi-coherent module over a
scheme. -/
def scheme (P : Property) {S : Scheme.{u}} (F : Scheme.QCoh S) : Prop :=
  match P.code with
  | .inl i =>
      match i.1 with
      | 0 => SheafOfModules.IsFree F.obj
      | 1 => SheafOfModules.IsFiniteFree F.obj
      | 2 => SheafOfModules.IsGloballyGenerated F.obj
      | 3 => SheafOfModules.IsFiniteGloballyGenerated F.obj
      | 4 => SheafOfModules.HasGlobalPresentation F.obj
      | 5 => SheafOfModules.HasFiniteGlobalPresentation F.obj
      | 6 => SheafOfModules.IsFiniteLocallyFree F.obj
      | 7 => SheafOfModules.IsLocallyGeneratedBySections F.obj
      | 8 => SheafOfModules.IsFiniteType F.obj
      | 9 => F.obj.IsQuasicoherent
      | 10 => SheafOfModules.IsFinitePresentation F.obj
      | 11 => SheafOfModules.IsFlat F.obj
      | _ => False
  | .inr (false, r) => SheafOfModules.IsGeneratedBy F.obj r
  | .inr (true, r) => SheafOfModules.IsLocallyGeneratedBy F.obj r

/-- The scheme-side interpretation of a property is its corresponding
canonical module predicate. -/
theorem scheme_apply (P : Property) {S : Scheme.{u}} (F : Scheme.QCoh S) :
    P.scheme F = match P.code with
      | .inl i =>
          match i.1 with
          | 0 => SheafOfModules.IsFree F.obj
          | 1 => SheafOfModules.IsFiniteFree F.obj
          | 2 => SheafOfModules.IsGloballyGenerated F.obj
          | 3 => SheafOfModules.IsFiniteGloballyGenerated F.obj
          | 4 => SheafOfModules.HasGlobalPresentation F.obj
          | 5 => SheafOfModules.HasFiniteGlobalPresentation F.obj
          | 6 => SheafOfModules.IsFiniteLocallyFree F.obj
          | 7 => SheafOfModules.IsLocallyGeneratedBySections F.obj
          | 8 => SheafOfModules.IsFiniteType F.obj
          | 9 => F.obj.IsQuasicoherent
          | 10 => SheafOfModules.IsFinitePresentation F.obj
          | 11 => SheafOfModules.IsFlat F.obj
          | _ => False
      | .inr (false, r) => SheafOfModules.IsGeneratedBy F.obj r
      | .inr (true, r) => SheafOfModules.IsLocallyGeneratedBy F.obj r := sorry

/-- Interpret an associated-module property on the image in a standard big
site. -/
def big (P : Property) (τ : StandardTopology) (S : Scheme.{u})
    (F : Scheme.QCoh S) : Prop :=
  match P.code with
  | .inl i =>
      match i.1 with
      | 0 => SheafOfModules.IsFree ((bigFunctor τ S).obj F).obj
      | 1 => SheafOfModules.IsFiniteFree ((bigFunctor τ S).obj F).obj
      | 2 => SheafOfModules.IsGloballyGenerated ((bigFunctor τ S).obj F).obj
      | 3 => SheafOfModules.IsFiniteGloballyGenerated ((bigFunctor τ S).obj F).obj
      | 4 => SheafOfModules.HasGlobalPresentation ((bigFunctor τ S).obj F).obj
      | 5 => SheafOfModules.HasFiniteGlobalPresentation ((bigFunctor τ S).obj F).obj
      | 6 => SheafOfModules.IsFiniteLocallyFree ((bigFunctor τ S).obj F).obj
      | 7 => SheafOfModules.IsLocallyGeneratedBySections ((bigFunctor τ S).obj F).obj
      | 8 => SheafOfModules.IsFiniteType ((bigFunctor τ S).obj F).obj
      | 9 => ((bigFunctor τ S).obj F).obj.IsQuasicoherent
      | 10 => SheafOfModules.IsFinitePresentation ((bigFunctor τ S).obj F).obj
      | 11 => SheafOfModules.RingedSite.IsFlat
          (bigCommStructureSheaf τ S) (bigComm τ S F.obj)
      | _ => False
  | .inr (false, r) =>
      SheafOfModules.IsGeneratedBy ((bigFunctor τ S).obj F).obj r
  | .inr (true, r) =>
      SheafOfModules.IsLocallyGeneratedBy ((bigFunctor τ S).obj F).obj r

/-- The big-site interpretation of a property is its corresponding canonical
module predicate. -/
theorem big_apply (P : Property) (τ : StandardTopology) (S : Scheme.{u})
    (F : Scheme.QCoh S) :
    P.big τ S F = match P.code with
      | .inl i =>
          match i.1 with
          | 0 => SheafOfModules.IsFree ((bigFunctor τ S).obj F).obj
          | 1 => SheafOfModules.IsFiniteFree ((bigFunctor τ S).obj F).obj
          | 2 => SheafOfModules.IsGloballyGenerated ((bigFunctor τ S).obj F).obj
          | 3 =>
              SheafOfModules.IsFiniteGloballyGenerated ((bigFunctor τ S).obj F).obj
          | 4 => SheafOfModules.HasGlobalPresentation ((bigFunctor τ S).obj F).obj
          | 5 =>
              SheafOfModules.HasFiniteGlobalPresentation ((bigFunctor τ S).obj F).obj
          | 6 => SheafOfModules.IsFiniteLocallyFree ((bigFunctor τ S).obj F).obj
          | 7 =>
              SheafOfModules.IsLocallyGeneratedBySections ((bigFunctor τ S).obj F).obj
          | 8 => SheafOfModules.IsFiniteType ((bigFunctor τ S).obj F).obj
          | 9 => ((bigFunctor τ S).obj F).obj.IsQuasicoherent
          | 10 => SheafOfModules.IsFinitePresentation ((bigFunctor τ S).obj F).obj
          | 11 => SheafOfModules.RingedSite.IsFlat
              (bigCommStructureSheaf τ S) (bigComm τ S F.obj)
          | _ => False
      | .inr (false, r) =>
          SheafOfModules.IsGeneratedBy ((bigFunctor τ S).obj F).obj r
      | .inr (true, r) =>
          SheafOfModules.IsLocallyGeneratedBy ((bigFunctor τ S).obj F).obj r := sorry

/-- Interpret an associated-module property on the image in a small standard
site. -/
def small (P : Property) (τ : StandardTopology) (S : Scheme.{u})
    (F : Scheme.QCoh S) : Prop :=
  match P.code with
  | .inl i =>
      match i.1 with
      | 0 => SheafOfModules.IsFree ((StandardSmall.functor τ S).obj F).obj
      | 1 => SheafOfModules.IsFiniteFree ((StandardSmall.functor τ S).obj F).obj
      | 2 => SheafOfModules.IsGloballyGenerated ((StandardSmall.functor τ S).obj F).obj
      | 3 =>
          SheafOfModules.IsFiniteGloballyGenerated ((StandardSmall.functor τ S).obj F).obj
      | 4 => SheafOfModules.HasGlobalPresentation ((StandardSmall.functor τ S).obj F).obj
      | 5 =>
          SheafOfModules.HasFiniteGlobalPresentation ((StandardSmall.functor τ S).obj F).obj
      | 6 => SheafOfModules.IsFiniteLocallyFree ((StandardSmall.functor τ S).obj F).obj
      | 7 =>
          SheafOfModules.IsLocallyGeneratedBySections ((StandardSmall.functor τ S).obj F).obj
      | 8 => SheafOfModules.IsFiniteType ((StandardSmall.functor τ S).obj F).obj
      | 9 => ((StandardSmall.functor τ S).obj F).obj.IsQuasicoherent
      | 10 =>
          SheafOfModules.IsFinitePresentation ((StandardSmall.functor τ S).obj F).obj
      | 11 => SheafOfModules.RingedSite.IsFlat
          (StandardSmall.commStructureSheaf τ S) (StandardSmall.comm τ S F.obj)
      | _ => False
  | .inr (false, r) =>
      SheafOfModules.IsGeneratedBy ((StandardSmall.functor τ S).obj F).obj r
  | .inr (true, r) =>
      SheafOfModules.IsLocallyGeneratedBy ((StandardSmall.functor τ S).obj F).obj r

/-- The small-site interpretation of a property is its corresponding canonical
module predicate. -/
theorem small_apply (P : Property) (τ : StandardTopology) (S : Scheme.{u})
    (F : Scheme.QCoh S) :
    P.small τ S F = match P.code with
      | .inl i =>
          match i.1 with
          | 0 => SheafOfModules.IsFree ((StandardSmall.functor τ S).obj F).obj
          | 1 => SheafOfModules.IsFiniteFree ((StandardSmall.functor τ S).obj F).obj
          | 2 =>
              SheafOfModules.IsGloballyGenerated ((StandardSmall.functor τ S).obj F).obj
          | 3 =>
              SheafOfModules.IsFiniteGloballyGenerated
                ((StandardSmall.functor τ S).obj F).obj
          | 4 =>
              SheafOfModules.HasGlobalPresentation ((StandardSmall.functor τ S).obj F).obj
          | 5 =>
              SheafOfModules.HasFiniteGlobalPresentation
                ((StandardSmall.functor τ S).obj F).obj
          | 6 =>
              SheafOfModules.IsFiniteLocallyFree ((StandardSmall.functor τ S).obj F).obj
          | 7 =>
              SheafOfModules.IsLocallyGeneratedBySections
                ((StandardSmall.functor τ S).obj F).obj
          | 8 => SheafOfModules.IsFiniteType ((StandardSmall.functor τ S).obj F).obj
          | 9 => ((StandardSmall.functor τ S).obj F).obj.IsQuasicoherent
          | 10 =>
              SheafOfModules.IsFinitePresentation ((StandardSmall.functor τ S).obj F).obj
          | 11 => SheafOfModules.RingedSite.IsFlat
              (StandardSmall.commStructureSheaf τ S) (StandardSmall.comm τ S F.obj)
          | _ => False
      | .inr (false, r) =>
          SheafOfModules.IsGeneratedBy ((StandardSmall.functor τ S).obj F).obj r
      | .inr (true, r) =>
          SheafOfModules.IsLocallyGeneratedBy
            ((StandardSmall.functor τ S).obj F).obj r := sorry

/-- Passage to an associated module on any standard big site preserves and
reflects every selected property. -/
theorem big_iff (P : Property) (τ : StandardTopology) (S : Scheme.{u})
    (F : Scheme.QCoh S) : P.scheme F ↔ P.big τ S F := sorry

/-- Passage to an associated module on any small standard site preserves and
reflects every selected property. -/
theorem small_iff (P : Property) (τ : StandardTopology) (S : Scheme.{u})
    (F : Scheme.QCoh S) : P.scheme F ↔ P.small τ S F := sorry

end Property

/-- On a locally Noetherian scheme, passage to the associated module on the
small Zariski or étale site preserves and reflects coherence. -/
theorem coherent_small_iff (σ : SmallStandardTopology) (S : Scheme.{u})
    [IsLocallyNoetherian S] (F : Scheme.QCoh S) :
    F.obj.IsCoherent ↔
      ((StandardSmall.functor σ.toStandard S).obj F).obj.IsCoherent := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
